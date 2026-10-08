-- Prove2me | solution 1 for ProcessingNetworks.PacketNetworks.back_pressure_irreducible_aperiodic
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T19:50:49.143146+00:00
-- url     : https://prove2.me/submissions/4ac8c08f-ca47-4fb8-9bda-59224dabb1e5

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_BackPressurePolicy
import Definitions.Def_ProcessingNetworks_PacketNetworks_BPAmbientChain
import Definitions.Def_ProcessingNetworks_PacketNetworks_MarkovianPolicy
import Definitions.Def_ProcessingNetworks_PacketNetworks_SchedulesAndConfigurations



namespace ProcessingNetworks.PacketNetworks

open MeasureTheory ProbabilityTheory

/-- class `a` is directly downstream of class `b` -/
def bpDown {I J : ℕ} (dat : PacketNetworkData I J) (a b : Fin I) : Prop :=
  ∃ j, dat.u j = b ∧ dat.d j = some a

theorem bpDown_wf {I J : ℕ} (dat : PacketNetworkData I J) (h121 : SatisfiesAssumption121 dat) :
    WellFounded (bpDown dat) := by
  refine ⟨fun x => ?_⟩
  by_contra hx
  obtain ⟨f, -, hf⟩ := not_acc_iff_exists_descending_chain.mp hx
  choose j hj using hf
  obtain ⟨a, b, hab, hjab⟩ := Finite.exists_ne_map_eq_of_infinite j
  wlog hlt : a < b generalizing a b
  · exact this b a hab.symm hjab.symm (lt_of_le_of_ne (not_lt.mp hlt) hab.symm)
  obtain ⟨n, rfl⟩ : ∃ n, b = a + (n + 1) := ⟨b - a - 1, by omega⟩
  apply h121.2 n (fun k => j (a + k.val))
  intro k
  show dat.d (j (a + k.val)) = some (dat.u (j (a + (k+1 : Fin (n+1)).val)))
  rw [(hj (a + k.val)).2]
  congr 1
  by_cases hk : k.val + 1 < n + 1
  · have : ((k + 1 : Fin (n+1))).val = k.val + 1 := by
      rw [Fin.val_add_one_of_lt]; exact Fin.lt_def.mpr (by simp; omega)
    rw [this, (hj (a + (k.val + 1))).1, add_assoc]
  · have hkn : k.val = n := by omega
    have : ((k + 1 : Fin (n+1))).val = 0 := by
      have : k = Fin.last n := Fin.ext (by simp [hkn])
      subst this; simp
    rw [this, add_zero, hjab, (hj (a + (n+1))).1, hkn, add_assoc]

open Classical in
/-- potential weights -/
noncomputable def bpW {I J : ℕ} (dat : PacketNetworkData I J) (i : Fin I) : ℕ :=
  (Finset.univ.filter (fun a => Relation.TransGen (bpDown dat) a i)).card + 1

theorem bpW_lt {I J : ℕ} (dat : PacketNetworkData I J) (h121 : SatisfiesAssumption121 dat)
    (j : Fin J) (i' : Fin I) (hd : dat.d j = some i') : bpW dat i' < bpW dat (dat.u j) := by
  classical
  have wf := (bpDown_wf dat h121).transGen
  have irr : ∀ a, ¬ Relation.TransGen (bpDown dat) a a := by
    intro a
    induction a using wf.induction with
    | _ a IH => intro h; exact IH a h h
  have hr : bpDown dat i' (dat.u j) := ⟨j, rfl, hd⟩
  unfold bpW
  apply Nat.add_lt_add_right
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨i', ?_, ?_⟩
    · simp; exact Relation.TransGen.single hr
    · simp; exact irr i'
  · intro x; simp; intro hx; exact hx.tail hr


theorem bp_coef {I J : ℕ} (dat : PacketNetworkData I J) (h121 : SatisfiesAssumption121 dat)
    (j : Fin J) : 1 ≤ ∑ i, (bpW dat i : ℤ) * Rint dat i j := by
  cases hd : dat.d j with
  | none =>
    simp [Rint, hd, bpW]
  | some i' =>
    have := bpW_lt dat h121 j i' hd
    simp [Rint, hd, mul_add, Finset.sum_add_distrib]
    omega

theorem bp_pot_lt {I J : ℕ} (dat : PacketNetworkData I J) (h121 : SatisfiesAssumption121 dat)
    (z y : Fin I → ℕ) (s : Fin J → ℕ) (hs : ∃ j, s j ≠ 0)
    (hy : (fun i => (y i : ℤ)) = nextState dat (fun i => (z i : ℤ)) 0 s) :
    ∑ i, bpW dat i * y i < ∑ i, bpW dat i * z i := by
  have key : (∑ i, (bpW dat i * y i : ℕ) : ℤ) = (∑ i, (bpW dat i * z i : ℕ) : ℤ)
      - ∑ j, (s j : ℤ) * ∑ i, (bpW dat i : ℤ) * Rint dat i j := by
    have h1 : ∀ i, (y i : ℤ) = z i - ∑ j, Rint dat i j * s j := by
      intro i; have := congrFun hy i; simp [nextState] at this; rw [this]
    simp only [Nat.cast_sum, Nat.cast_mul, h1, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  have hpos : (1 : ℤ) ≤ ∑ j, (s j : ℤ) * ∑ i, (bpW dat i : ℤ) * Rint dat i j := by
    obtain ⟨j0, hj0⟩ := hs
    calc (1 : ℤ) ≤ (s j0 : ℤ) * ∑ i, (bpW dat i : ℤ) * Rint dat i j0 := by
          have := bp_coef dat h121 j0
          have : (1 : ℤ) ≤ s j0 := by omega
          nlinarith
      _ ≤ _ := by
          apply Finset.single_le_sum (f := fun j => (s j : ℤ) * ∑ i, (bpW dat i : ℤ) * Rint dat i j)
            _ (Finset.mem_univ j0)
          intro j _
          have := bp_coef dat h121 j
          positivity
  have : ((∑ i, bpW dat i * y i : ℕ) : ℤ) < ((∑ i, bpW dat i * z i : ℕ) : ℤ) := by
    push_cast at key ⊢; linarith
  exact_mod_cast this

theorem bp_nonneg {I J : ℕ} (dat : PacketNetworkData I J) (z : Fin I → ℕ) (e : Fin I → ℕ)
    (s : Fin J → ℕ) (hBs : ∀ i, (B dat).mulVec (realize s) i ≤ (z i : ℝ)) :
    ∃ y : Fin I → ℕ, (fun i => (y i : ℤ)) = nextState dat (fun i => (z i : ℤ)) e s := by
  have hnn : ∀ i, 0 ≤ nextState dat (fun i => (z i : ℤ)) e s i := by
    intro i
    have h1 : ∑ j, Rint dat i j * (s j : ℤ) ≤ ∑ j, (if dat.u j = i then (1:ℤ) else 0) * s j := by
      apply Finset.sum_le_sum; intro j _
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      unfold Rint; split_ifs <;> simp
    have h2 : ((∑ j, (if dat.u j = i then (1:ℤ) else 0) * (s j : ℤ) : ℤ) : ℝ) ≤ (z i : ℝ) := by
      refine le_trans (le_of_eq ?_) (hBs i)
      push_cast
      simp [B, Matrix.mulVec, dotProduct, realize]
    have h3 : (∑ j, (if dat.u j = i then (1:ℤ) else 0) * (s j : ℤ) : ℤ) ≤ (z i : ℤ) := by
      exact_mod_cast h2
    simp only [nextState]
    have : (0:ℤ) ≤ e i := by positivity
    linarith
  refine ⟨fun i => (nextState dat (fun i => (z i : ℤ)) e s i).toNat, ?_⟩
  funext i
  simp [Int.toNat_of_nonneg (hnn i)]

theorem bp_single_mem {I J K : ℕ} (dat : PacketNetworkData I J)
    (cfg : LinkConfigData J K) (h124 : SatisfiesAssumption124 cfg)
    (S : Finset (Fin J → ℕ)) (hS : IsScheduleSet cfg S) (j : Fin J) :
    (Pi.single j 1 : Fin J → ℕ) ∈ S := by
  rw [hS]
  obtain ⟨k0, hk0, huniq⟩ := cfg.hA j
  obtain ⟨c, hc, hck⟩ := h124 k0
  refine ⟨c, hc, ?_⟩
  intro k
  have hmv : cfg.A.mulVec (fun j' => ((Pi.single j 1 : Fin J → ℕ) j' : ℝ)) k = cfg.A k j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hmv]
  by_cases hk : cfg.A k j = 1
  · rw [huniq k hk, hk0]; exact_mod_cast hck
  · rw [cfg.hA0 j k hk]; positivity

theorem bp_obj_single {I J : ℕ} (dat : PacketNetworkData I J) (z : Fin I → ℝ) (j : Fin J) :
    bpObjective dat z (Pi.single j 1) = ∑ i, z i * R dat i j := by
  simp [bpObjective, Matrix.mulVec, dotProduct, realize, Pi.single_apply]

theorem bp_nonzero {I J K : ℕ} (dat : PacketNetworkData I J) (h121 : SatisfiesAssumption121 dat)
    (cfg : LinkConfigData J K) (h124 : SatisfiesAssumption124 cfg)
    (S : Finset (Fin J → ℕ)) (hS : IsScheduleSet cfg S) (z : Fin I → ℕ) (hz : z ≠ 0)
    (s : Fin J → ℕ) (hopt : IsBPOptimal dat S (fun i => (z i : ℝ)) s) : ∃ j, s j ≠ 0 := by
  classical
  -- find a good activity
  obtain ⟨k, hk⟩ : ∃ k, z k ≠ 0 := by
    by_contra h; push_neg at h; exact hz (funext h)
  have hne : (Finset.univ : Finset (Fin I)).Nonempty := ⟨k, Finset.mem_univ _⟩
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ z hne
  set T := Finset.univ.filter (fun i => z i = z m) with hT
  have hTne : T.Nonempty := ⟨m, by simp [hT]⟩
  obtain ⟨i, hiT, hi⟩ := Finset.exists_min_image T (bpW dat) hTne
  have hzi : z i = z m := by simpa [hT] using hiT
  have hzi1 : 1 ≤ z i := by have := hm k (Finset.mem_univ _); omega
  obtain ⟨j, hj⟩ := h121.1 i
  have hobj : 0 < bpObjective dat (fun i => (z i : ℝ)) (Pi.single j 1) := by
    rw [bp_obj_single]
    cases hd : dat.d j with
    | none =>
      simp [R, hd, hj]; exact_mod_cast hzi1
    | some i' =>
      have hsum : ∑ x, (z x : ℝ) * R dat x j = z i - z i' := by
        simp [R, hd, hj, mul_add, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
        ring
      rw [hsum]
      have hw := bpW_lt dat h121 j i' hd
      rw [hj] at hw
      have hle : z i' ≤ z m := hm i' (Finset.mem_univ _)
      have hlt : z i' < z i := by
        rcases lt_or_eq_of_le hle with h | h
        · omega
        · exfalso
          have := hi i' (by simp [hT, h])
          omega
      have : (z i' : ℝ) < z i := by exact_mod_cast hlt
      linarith
  have hfeas : (Pi.single j 1 : Fin J → ℕ) ∈ feasibleSchedulesAt dat S (fun i => (z i : ℝ)) := by
    simp only [feasibleSchedulesAt, Finset.mem_filter]
    refine ⟨bp_single_mem dat cfg h124 S hS j, ?_⟩
    intro i''
    have : (B dat).mulVec (realize (Pi.single j 1 : Fin J → ℕ)) i'' = B dat i'' j := by
      simp [Matrix.mulVec, dotProduct, realize, Pi.single_apply]
    rw [this]
    simp only [B]
    split_ifs with h
    · rw [← h, hj]; exact_mod_cast hzi1
    · positivity
  have h2 := hopt.2 _ hfeas
  by_contra hs
  push_neg at hs
  have : s = 0 := funext hs
  subst this
  have : bpObjective dat (fun i => (z i : ℝ)) 0 = 0 := by
    have hr : realize (0 : Fin J → ℕ) = 0 := by funext j; simp [realize]
    simp [bpObjective, hr]
  linarith

theorem bp_jump_lb {I J : ℕ} {Ω : Type*} [MeasureSpace Ω] (dat : PacketNetworkData I J)
    (P : PacketPrimitives I J Ω) (hmeas : ∀ z, Measurable (P.f z))
    (jump : (Fin I → ℕ) → PMF (Fin I → ℕ)) (hjump : IsPolicyChain dat P jump)
    (z y : Fin I → ℕ) :
    ℙ {ω | P.Eincr 1 ω = 0} *
      volume ({u : ℝ | (fun i => (y i : ℤ)) = nextState dat (fun i => (z i : ℤ)) 0 (P.f z u)}
        ∩ Set.Ioo (0 : ℝ) 1) ≤ jump z y := by
  set A := {u : ℝ | (fun i => (y i : ℤ)) = nextState dat (fun i => (z i : ℤ)) 0 (P.f z u)} with hAdef
  have hA : MeasurableSet A := by
    have : A = P.f z ⁻¹' {s | (fun i => (y i : ℤ)) = nextState dat (fun i => (z i : ℤ)) 0 s} := rfl
    rw [this]
    exact hmeas z (Set.to_countable _).measurableSet
  rw [hjump z y]
  calc ℙ {ω | P.Eincr 1 ω = 0} * volume (A ∩ Set.Ioo (0 : ℝ) 1)
      = ∫⁻ u in Set.Ioo (0 : ℝ) 1, A.indicator (fun _ => ℙ {ω | P.Eincr 1 ω = 0}) u := by
        rw [lintegral_indicator_const hA, Measure.restrict_apply hA]
    _ ≤ _ := by
        apply lintegral_mono
        intro u
        by_cases hu : u ∈ A
        · rw [Set.indicator_of_mem hu]
          refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (0 : Fin I → ℕ))
          exact (if_pos hu).symm
        · simp [Set.indicator_of_notMem hu]

theorem bp_step_succ {X : Type*} (jump : X → PMF X) (x y w : X) (n : ℕ)
    (h1 : 0 < jump x y) (h2 : 0 < stepIter jump n y w) : 0 < stepIter jump (n + 1) x w := by
  show 0 < ((jump x).bind (Stability.stepIter jump n)) w
  rw [PMF.bind_apply]
  exact lt_of_lt_of_le (ENNReal.mul_pos h1.ne' h2.ne') (ENNReal.le_tsum y)

theorem bp_step_trans {X : Type*} (jump : X → PMF X) (m n : ℕ) :
    ∀ x w y : X, 0 < stepIter jump m x w → 0 < stepIter jump n w y →
      0 < stepIter jump (m + n) x y := by
  induction m with
  | zero =>
    intro x w y h1 h2
    have : stepIter jump 0 x = PMF.pure x := rfl
    rw [this, PMF.pure_apply] at h1
    split_ifs at h1 with h
    · subst h; simpa using h2
    · simp at h1
  | succ m ih =>
    intro x w y h1 h2
    have : stepIter jump (m + 1) x = (jump x).bind (stepIter jump m) := rfl
    rw [this, PMF.bind_apply] at h1
    obtain ⟨a, ha⟩ : ∃ a, jump x a * stepIter jump m a w ≠ 0 := by
      by_contra hc
      push_neg at hc
      rw [ENNReal.tsum_eq_zero.mpr hc] at h1
      exact lt_irrefl _ h1
    obtain ⟨ha1, ha2⟩ := mul_ne_zero_iff.mp ha
    have := bp_step_succ jump x a y (m + n) (pos_iff_ne_zero.mpr ha1)
      (ih a w y (pos_iff_ne_zero.mpr ha2) h2)
    rwa [show m + 1 + n = m + n + 1 by omega]

theorem bp_feas_le {I J : ℕ} (dat : PacketNetworkData I J) (S : Finset (Fin J → ℕ))
    (z : Fin I → ℕ) (s : Fin J → ℕ) (h : IsBPOptimal dat S (fun i => (z i : ℝ)) s) :
    ∀ i, (B dat).mulVec (realize s) i ≤ (z i : ℝ) := by
  have := h.1
  simp only [feasibleSchedulesAt, Finset.mem_filter] at this
  exact this.2

theorem bp_part1 {I J K : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (dat : PacketNetworkData I J) (h121 : SatisfiesAssumption121 dat)
    (cfg : LinkConfigData J K) (h124 : SatisfiesAssumption124 cfg)
    (S : Finset (Fin J → ℕ)) (hS : IsScheduleSet cfg S)
    (lam : Fin I → ℝ) (P : PacketPrimitives I J Ω) (hP : PrimitiveAssumptions P lam)
    (hBP : IsBackPressurePolicy dat S P.f)
    (jump : (Fin I → ℕ) → PMF (Fin I → ℕ)) (hjump : IsPolicyChain dat P jump) :
    ∀ z : Fin I → ℕ, ∃ n, 0 < stepIter jump n z 0 := by
  intro z
  induction h : ∑ i, bpW dat i * z i using Nat.strong_induction_on generalizing z with
  | _ N IH =>
  by_cases hz : z = 0
  · subst hz
    refine ⟨0, ?_⟩
    show 0 < (PMF.pure (0 : Fin I → ℕ)) 0
    simp
  obtain ⟨y, hjy, hpot⟩ : ∃ y, 0 < jump z y ∧ ∑ i, bpW dat i * y i < ∑ i, bpW dat i * z i := by
    by_contra hc
    let A : (Fin I → ℕ) → Set ℝ := fun y =>
      {u : ℝ | (fun i => (y i : ℤ)) = nextState dat (fun i => (z i : ℤ)) 0 (P.f z u)}
        ∩ Set.Ioo (0 : ℝ) 1
    have hnull : ∀ y, volume (A y) = 0 := by
      intro y
      by_contra hne
      obtain ⟨u, hu1, hu2⟩ := MeasureTheory.nonempty_of_measure_ne_zero hne
      have hopt := hBP z u hu2.1 hu2.2
      have hp := bp_pot_lt dat h121 z y (P.f z u)
        (bp_nonzero dat h121 cfg h124 S hS z hz _ hopt) hu1
      have hlb := bp_jump_lb dat P hP.policy_measurable jump hjump z y
      have hpos : 0 < ℙ {ω | P.Eincr 1 ω = 0} * volume (A y) :=
        ENNReal.mul_pos hP.arrival_zero.ne' hne
      exact hc ⟨y, lt_of_lt_of_le hpos hlb, hp⟩
    have hsub : Set.Ioo (0 : ℝ) 1 ⊆ ⋃ y, A y := by
      intro u hu
      obtain ⟨y, hy⟩ := bp_nonneg dat z 0 (P.f z u) (bp_feas_le dat S z _ (hBP z u hu.1 hu.2))
      exact Set.mem_iUnion.mpr ⟨y, hy, hu⟩
    have h0 : volume (Set.Ioo (0 : ℝ) 1) = 0 :=
      measure_mono_null hsub (measure_iUnion_null hnull)
    simp [Real.volume_Ioo] at h0
  obtain ⟨n, hn⟩ := IH _ (h ▸ hpot) y rfl
  exact ⟨n + 1, bp_step_succ jump z y 0 n hjy hn⟩

theorem bp_loop {I J K : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (dat : PacketNetworkData I J)
    (S : Finset (Fin J → ℕ))
    (lam : Fin I → ℝ) (P : PacketPrimitives I J Ω) (hP : PrimitiveAssumptions P lam)
    (hBP : IsBackPressurePolicy dat S P.f)
    (jump : (Fin I → ℕ) → PMF (Fin I → ℕ)) (hjump : IsPolicyChain dat P jump) :
    0 < jump 0 0 := by
  have hlb := bp_jump_lb dat P hP.policy_measurable jump hjump 0 0
  refine lt_of_lt_of_le (ENNReal.mul_pos hP.arrival_zero.ne' ?_) hlb
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆
      {u : ℝ | (fun i => ((0 : Fin I → ℕ) i : ℤ)) =
        nextState dat (fun i => ((0 : Fin I → ℕ) i : ℤ)) 0 (P.f 0 u)} ∩ Set.Ioo (0 : ℝ) 1 := by
    intro u hu
    refine ⟨?_, hu⟩
    have hle := bp_feas_le dat S 0 _ (hBP 0 u hu.1 hu.2)
    have hs : P.f 0 u = 0 := by
      funext j
      have h1 := hle (dat.u j)
      have h2 : ((P.f 0 u j : ℕ) : ℝ) ≤ (B dat).mulVec (realize (P.f 0 u)) (dat.u j) := by
        simp only [B, Matrix.mulVec, dotProduct, realize]
        refine le_trans (le_of_eq ?_) (Finset.single_le_sum
          (f := fun j' => (if dat.u j' = dat.u j then (1:ℝ) else 0) * (P.f 0 u j' : ℝ))
          (fun j' _ => by positivity) (Finset.mem_univ j))
        simp
      have : ((P.f 0 u j : ℕ) : ℝ) ≤ 0 := by simpa using h2.trans h1
      simp only [Pi.zero_apply]
      exact_mod_cast le_antisymm this (by positivity)
    simp only [Set.mem_setOf_eq]
    rw [hs]
    funext i
    simp [nextState]
  have := measure_mono (μ := volume) hsub
  rw [Real.volume_Ioo] at this
  intro h0
  rw [h0] at this
  simp at this

theorem bp_core {I J K : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (dat : PacketNetworkData I J) (h121 : SatisfiesAssumption121 dat)
    (cfg : LinkConfigData J K) (h124 : SatisfiesAssumption124 cfg)
    (S : Finset (Fin J → ℕ)) (hS : IsScheduleSet cfg S)
    (lam : Fin I → ℝ) (P : PacketPrimitives I J Ω) (hP : PrimitiveAssumptions P lam)
    (hBP : IsBackPressurePolicy dat S P.f)
    (jump : (Fin I → ℕ) → PMF (Fin I → ℕ)) (hjump : IsPolicyChain dat P jump) :
    (∀ z : Fin I → ℕ, (0 : Fin I → ℕ) ∈ reachableFrom jump z) ∧
      IrreducibleOn jump (reachableFrom jump 0) ∧
      AperiodicOn jump (reachableFrom jump 0) := by
  have h1 := bp_part1 dat h121 cfg h124 S hS lam P hP hBP jump hjump
  have hl := bp_loop (K := K) dat S lam P hP hBP jump hjump
  refine ⟨fun z => h1 z, ?_, ?_⟩
  · intro x _ y hy
    obtain ⟨m, hm⟩ := h1 x
    obtain ⟨n, hn⟩ := hy
    exact ⟨m + n, bp_step_trans jump m n x 0 y hm hn⟩
  · intro x hx d hd
    obtain ⟨m, hm⟩ := h1 x
    obtain ⟨n, hn⟩ := hx
    have hloop : 0 < stepIter jump 1 (0 : Fin I → ℕ) 0 :=
      bp_step_succ jump 0 0 0 0 hl (by show 0 < (PMF.pure (0 : Fin I → ℕ)) 0; simp)
    have hA : 0 < stepIter jump (m + (1 + n)) x x :=
      bp_step_trans jump m (1 + n) x 0 x hm (bp_step_trans jump 1 n 0 0 x hloop hn)
    have dA := hd _ (by omega) hA
    by_cases hmn : m + n = 0
    · have : m + (1 + n) = 1 := by omega
      rw [this] at dA
      exact Nat.dvd_one.mp dA
    · have hB : 0 < stepIter jump (m + n) x x := bp_step_trans jump m n x 0 x hm hn
      have dB := hd _ (by omega) hB
      have : m + (1 + n) = (m + n) + 1 := by omega
      rw [this] at dA
      exact Nat.dvd_one.mp ((Nat.dvd_add_right dB).mp dA)

end ProcessingNetworks.PacketNetworks

open ProcessingNetworks.PacketNetworks
open ProcessingNetworks.PacketNetworks MeasureTheory ProbabilityTheory

theorem solution
    {I J K : ℕ} {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (dat : PacketNetworkData I J) (h121 : SatisfiesAssumption121 dat)
    (cfg : LinkConfigData J K) (h124 : SatisfiesAssumption124 cfg)
    (S : Finset (Fin J → ℕ)) (hS : IsScheduleSet cfg S)
    (lam : Fin I → ℝ) (P : PacketPrimitives I J Ω) (hP : PrimitiveAssumptions P lam)
    (hBP : IsBackPressurePolicy dat S P.f)
    (jump : (Fin I → ℕ) → PMF (Fin I → ℕ)) (hjump : IsPolicyChain dat P jump) :
    (∀ z : Fin I → ℕ, (0 : Fin I → ℕ) ∈ reachableFrom jump z) ∧
      IrreducibleOn jump (reachableFrom jump 0) ∧
      AperiodicOn jump (reachableFrom jump 0) := by
  exact bp_core dat h121 cfg h124 S hS lam P hP hBP jump hjump
