-- Prove2me | solution 1 for StochApproxDyn.LimitSet.internallyChainTransitive_tfae
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T03:30:50.441807+00:00
-- url     : https://prove2.me/submissions/d61fef89-58f2-4062-a766-4a80688594f5

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence
import Definitions.Def_StochApproxDyn_LimitSet_Attractor

open scoped NNReal


namespace StochApproxDyn.Lyapunov

theorem flow_cont_at {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (s : ℝ≥0) :
    Continuous (fun x => Φ s x) := Φ.continuous continuous_const continuous_id

/-- step 1: tube lemma -/
theorem att_step1 {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (U K : Set M) (hUo : IsOpen U) (hK : IsCompact K)
    (T : ℝ≥0) (hTU : Φ T '' K ⊆ U) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ s : ℝ≥0, T ≤ s → s ≤ T + δ → Φ s '' K ⊆ U := by
  have hn : IsOpen {p : ℝ≥0 × M | Φ p.1 p.2 ∈ U} :=
    hUo.preimage (Φ.continuous continuous_fst continuous_snd)
  have hsub : ({T} : Set ℝ≥0) ×ˢ K ⊆ {p : ℝ≥0 × M | Φ p.1 p.2 ∈ U} := by
    rintro ⟨a, x⟩ ⟨ha, hx⟩
    simp only [Set.mem_singleton_iff] at ha
    subst ha
    exact hTU ⟨x, hx, rfl⟩
  obtain ⟨u, v, hu, hv, hTu, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hK hn hsub
  have hTu' : T ∈ u := hTu rfl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu T hTu'
  refine ⟨(ε / 2).toNNReal, by simpa using hε, ?_⟩
  · intro s h1 h2
    rintro _ ⟨x, hx, rfl⟩
    have hs : s ∈ u := by
      apply hball
      rw [Metric.mem_ball, NNReal.dist_eq]
      have h1' : (T : ℝ) ≤ s := h1
      have h2' : (s : ℝ) ≤ T + ε / 2 := by
        have := (NNReal.coe_le_coe.mpr h2)
        rw [NNReal.coe_add, Real.coe_toNNReal _ (by linarith)] at this; exact this
      rw [abs_lt]; constructor <;> linarith
    exact huv (Set.mk_mem_prod hs (hKv hx))

theorem att_step3 {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (U K : Set M) (hUK : U ⊆ K) (T : ℝ≥0) (hT : 0 < T) (δ : ℝ≥0) (hδ : 0 < δ)
    (hG : ∀ s : ℝ≥0, T ≤ s → s ≤ T + δ → Φ s '' K ⊆ U) :
    ∃ t0 : ℝ≥0, ∀ t : ℝ≥0, t0 ≤ t → Φ t '' K ⊆ U := by
  have hadd : ∀ a b : ℝ≥0, Φ a '' K ⊆ U → Φ b '' K ⊆ U → Φ (a + b) '' K ⊆ U := by
    intro a b ha hb
    rintro _ ⟨x, hx, rfl⟩
    rw [Φ.map_add]
    exact ha ⟨_, hUK (hb ⟨x, hx, rfl⟩), rfl⟩
  have hmul : ∀ h : ℝ≥0, Φ h '' K ⊆ U → ∀ n : ℕ, Φ ((n + 1 : ℕ) * h) '' K ⊆ U := by
    intro h hh n
    induction n with
    | zero => simpa using hh
    | succ k ih =>
      have : ((k + 1 + 1 : ℕ) : ℝ≥0) * h = h + ((k + 1 : ℕ) : ℝ≥0) * h := by push_cast; ring
      rw [this]; exact hadd _ _ hh ih
  refine ⟨((⌈(T : ℝ) / δ⌉₊ : ℕ) + 1 : ℝ≥0) * T, ?_⟩
  intro t ht
  set N := ⌈(T : ℝ) / δ⌉₊ with hN
  set n := ⌊(t : ℝ) / T⌋₊ with hn
  have hTr : (0 : ℝ) < T := hT
  have hδr : (0 : ℝ) < δ := hδ
  have ht' : ((N : ℝ) + 1) * T ≤ t := by
    have := NNReal.coe_le_coe.mpr ht; push_cast at this; exact this
  have hNn : N + 1 ≤ n := by
    rw [hn]; apply Nat.le_floor
    rw [le_div_iff₀ hTr]; push_cast; exact ht'
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hfl1 : (n : ℝ) ≤ t / T := Nat.floor_le (by positivity)
  have hfl2 : (t : ℝ) / T < n + 1 := Nat.lt_floor_add_one _
  have hNle : (T : ℝ) / δ ≤ N := Nat.le_ceil _
  set h : ℝ≥0 := t / (n : ℝ≥0) with hh
  have hhc : (h : ℝ) = t / n := by rw [hh, NNReal.coe_div]; rfl
  have hTh : T ≤ h := by
    rw [← NNReal.coe_le_coe, hhc]
    rw [le_div_iff₀ hnpos]; rw [le_div_iff₀ hTr] at hfl1; linarith
  have hhd : h ≤ T + δ := by
    rw [← NNReal.coe_le_coe, hhc, NNReal.coe_add]
    rw [div_le_iff₀ hnpos]
    rw [div_lt_iff₀ hTr] at hfl2
    rw [div_le_iff₀ hδr] at hNle
    have : (T : ℝ) ≤ n * δ := by
      have : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
      nlinarith
    nlinarith
  have := hmul h (hG h hTh hhd) (n - 1)
  have heq : (((n - 1 + 1 : ℕ)) : ℝ≥0) * h = t := by
    rw [Nat.sub_add_cancel hn1]
    rw [← NNReal.coe_inj]; push_cast; rw [hhc]; field_simp
  rwa [heq] at this

theorem exists_attractor_core {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (U : Set M) (hUo : IsOpen U) (hUne : U.Nonempty) (hUc : IsCompact (closure U))
    (T : ℝ≥0) (hT : 0 < T) (hTU : Φ T '' closure U ⊆ U) :
    ∃ A : Set M, StochApproxDyn.LimitSet.IsAttractor Φ A ∧ A ⊆ U ∧
      closure U ⊆ StochApproxDyn.LimitSet.basin Φ A := by
  set K := closure U with hKdef
  have hUK : U ⊆ K := subset_closure
  obtain ⟨δ, hδ, hG⟩ := att_step1 Φ U K hUo hUc T hTU
  obtain ⟨t0, ht0⟩ := att_step3 Φ U K hUK T hT δ hδ hG
  set S : ℝ≥0 → Set M := fun s => Φ s '' K with hS
  have hSc : ∀ s, IsCompact (S s) := fun s => hUc.image (flow_cont_at Φ s)
  have hScl : ∀ s, IsClosed (S s) := fun s => (hSc s).isClosed
  have hSne : ∀ s, (S s).Nonempty := fun s => (hUne.mono hUK).image _
  have hmono : ∀ r s : ℝ≥0, r + t0 ≤ s → S s ⊆ S r := by
    intro r s hrs
    rintro _ ⟨x, hx, rfl⟩
    have : s = r + (s - r) := by
      rw [add_tsub_cancel_of_le]; exact le_trans (le_add_of_nonneg_right zero_le') hrs
    refine ⟨Φ (s - r) x, hUK (ht0 (s - r) ?_ ⟨x, hx, rfl⟩), ?_⟩
    · rw [le_tsub_iff_left (le_trans (le_add_of_nonneg_right zero_le') hrs)]; exact hrs
    · show Φ r (Φ (s - r) x) = Φ s x
      rw [← Φ.map_add, ← this]
  have hdir : Directed (· ⊇ ·) S := by
    intro i j
    refine ⟨max i j + t0, hmono i _ ?_, hmono j _ ?_⟩
    · exact add_le_add (le_max_left _ _) le_rfl
    · exact add_le_add (le_max_right _ _) le_rfl
  set A := ⋂ s, S s with hA
  have hAne : A.Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed S hdir hSne hSc hScl
  have hAsub : ∀ s, A ⊆ S s := fun s => Set.iInter_subset _ s
  have hAc : IsCompact A := (hSc 0).of_isClosed_subset (isClosed_iInter hScl) (hAsub 0)
  have hAU : A ⊆ U := (hAsub t0).trans (ht0 t0 le_rfl)
  have hinv : StochApproxDyn.LimitSet.IsInvariantSet Φ A := by
    intro t
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      simp only [hA, Set.mem_iInter]
      intro r
      obtain ⟨x, hx, hxz⟩ := hAsub (r + t0) hz
      refine ⟨Φ (t + t0) x, hUK (ht0 _ (le_add_of_nonneg_left zero_le') ⟨x, hx, rfl⟩), ?_⟩
      show Φ r (Φ (t + t0) x) = Φ t z
      rw [← hxz, ← Φ.map_add, ← Φ.map_add]
      congr 1; ring
    · intro y hy
      set C : ℝ≥0 → Set M := fun s => S s ∩ (fun z => Φ t z) ⁻¹' {y} with hC
      have hCcl : ∀ s, IsClosed (C s) := fun s =>
        (hScl s).inter (isClosed_singleton.preimage (flow_cont_at Φ t))
      have hCc : ∀ s, IsCompact (C s) := fun s => (hSc s).of_isClosed_subset (hCcl s)
        Set.inter_subset_left
      have hCne : ∀ s, (C s).Nonempty := by
        intro s
        obtain ⟨x, hx, hxy⟩ := hAsub (t + s) hy
        refine ⟨Φ s x, ⟨x, hx, rfl⟩, ?_⟩
        show Φ t (Φ s x) = y
        rw [← Φ.map_add]; exact hxy
      have hCdir : Directed (· ⊇ ·) C := by
        intro i j
        refine ⟨max i j + t0, ?_, ?_⟩
        · exact Set.inter_subset_inter_left _ (hmono i _ (add_le_add (le_max_left _ _) le_rfl))
        · exact Set.inter_subset_inter_left _ (hmono j _ (add_le_add (le_max_right _ _) le_rfl))
      obtain ⟨z, hz⟩ :=
        IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hCdir hCne hCc hCcl
      simp only [Set.mem_iInter] at hz
      refine ⟨z, ?_, (hz 0).2⟩
      simp only [hA, Set.mem_iInter]
      intro s; exact (hz s).1
  have hunif : ∀ ε : ℝ, 0 < ε → ∃ t₁ : ℝ≥0, ∀ t : ℝ≥0, t₁ ≤ t → ∀ x ∈ K,
      Metric.infDist (Φ t x) A < ε := by
    intro ε hε
    have : ∃ s, S s ⊆ {y | Metric.infDist y A < ε} := by
      by_contra hcon
      push_neg at hcon
      set D : ℝ≥0 → Set M := fun s => S s ∩ {y | ε ≤ Metric.infDist y A} with hD
      have hDcl : ∀ s, IsClosed (D s) := fun s =>
        (hScl s).inter (isClosed_le continuous_const (Metric.continuous_infDist_pt A))
      have hDc : ∀ s, IsCompact (D s) := fun s => (hSc s).of_isClosed_subset (hDcl s)
        Set.inter_subset_left
      have hDne : ∀ s, (D s).Nonempty := by
        intro s
        obtain ⟨y, hy1, hy2⟩ := Set.not_subset.mp (hcon s)
        exact ⟨y, hy1, show ε ≤ Metric.infDist y A from le_of_not_gt hy2⟩
      have hDdir : Directed (· ⊇ ·) D := by
        intro i j
        refine ⟨max i j + t0, ?_, ?_⟩
        · exact Set.inter_subset_inter_left _ (hmono i _ (add_le_add (le_max_left _ _) le_rfl))
        · exact Set.inter_subset_inter_left _ (hmono j _ (add_le_add (le_max_right _ _) le_rfl))
      obtain ⟨z, hz⟩ :=
        IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed D hDdir hDne hDc hDcl
      simp only [Set.mem_iInter] at hz
      have hzA : z ∈ A := by
        simp only [hA, Set.mem_iInter]; intro s; exact (hz s).1
      have h1 := (hz 0).2
      simp only [Set.mem_setOf_eq, Metric.infDist_zero_of_mem hzA] at h1
      linarith
    obtain ⟨s, hs⟩ := this
    refine ⟨s + t0, fun t ht x hx => hs (hmono s t ht ⟨x, hx, rfl⟩)⟩
  refine ⟨A, ⟨hAne, hAc, hinv, U, hUo.mem_nhdsSet.mpr hAU, ?_⟩, hAU, ?_⟩
  · intro ε hε
    obtain ⟨t₁, h⟩ := hunif ε hε
    exact ⟨t₁, fun t ht x hx => h t ht x (hUK hx)⟩
  · intro x hx
    show Filter.Tendsto (fun t : ℝ≥0 => Metric.infDist (Φ t x) A) Filter.atTop (nhds 0)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨t₁, h⟩ := hunif ε hε
    refine ⟨t₁, fun t ht => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
    exact h t ht x hx

open StochApproxDyn.LimitSet in
theorem ict_preconnected {X : Type*} [MetricSpace X] [CompactSpace X] (ψ : Flow ℝ≥0 X)
    (hct : ∀ a b : X, ChainTo ψ a b) : PreconnectedSpace X := by
  rw [preconnectedSpace_iff_clopen]
  intro C hC
  by_contra hcon
  push_neg at hcon
  obtain ⟨hC1, hC2⟩ := hcon
  obtain ⟨a, ha⟩ := hC1
  obtain ⟨b, hb⟩ : ∃ b, b ∉ C := by
    by_contra h; push_neg at h; exact hC2 (Set.eq_univ_of_forall h)
  have hfl : ∀ x ∈ C, ∀ t : ℝ≥0, ψ t x ∈ C := by
    intro x hx t
    have hcl : IsClopen ((fun s : ℝ≥0 => ψ s x) ⁻¹' C) :=
      hC.preimage (ψ.continuous continuous_id continuous_const)
    have : (fun s : ℝ≥0 => ψ s x) ⁻¹' C = Set.univ :=
      hcl.eq_univ ⟨0, by simp [Flow.map_zero_apply, hx]⟩
    have ht : t ∈ (fun s : ℝ≥0 => ψ s x) ⁻¹' C := by rw [this]; trivial
    exact ht
  obtain ⟨δ, hδ, hth⟩ := hC.isClosed.isCompact.exists_thickening_subset_open hC.isOpen le_rfl
  have hstep : ∀ y z, y ∈ C → dist z y < δ → z ∈ C := by
    intro y z hy hzy
    exact hth (Metric.mem_thickening_iff.mpr ⟨y, hy, hzy⟩)
  obtain ⟨k, y, t, hk, hT, h0, hj, hkb⟩ := hct a b δ hδ 1 one_pos
  have hall : ∀ j, j ≤ k → y j ∈ C := by
    intro j
    induction j with
    | zero => intro _; exact hstep a _ ha h0
    | succ i ih =>
      intro hi
      have hyi := ih (by omega)
      have := hj i (by omega)
      exact hstep _ _ (hfl _ hyi _) (by rw [dist_comm]; exact this)
  exact hb (hkb ▸ hall k le_rfl)

open StochApproxDyn.LimitSet in
theorem attractor_isOpen_of_chainRec {X : Type*} [MetricSpace X] (ψ : Flow ℝ≥0 X)
    (hcr : ∀ p : X, ChainTo ψ p p) (A : Set X) (hA : IsAttractor ψ A) : IsOpen A := by
  obtain ⟨hne, hc, hinv, W, hW, hunif⟩ := hA
  have hAW : A ⊆ interior W := subset_interior_iff_mem_nhdsSet.mpr hW
  suffices h : interior W ⊆ A by
    have : A = interior W := Set.Subset.antisymm hAW h
    rw [this]; exact isOpen_interior
  intro x hx
  by_contra hxA
  have hr : 0 < Metric.infDist x A := (hc.isClosed.notMem_iff_infDist_pos hne).1 hxA
  obtain ⟨ε1, hε1, hth⟩ := hc.exists_thickening_subset_open isOpen_interior hAW
  set ε := min ε1 (Metric.infDist x A) with hε
  have hεpos : 0 < ε := lt_min hε1 hr
  obtain ⟨t1, ht1⟩ := hunif (ε / 2) (by linarith)
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  obtain ⟨k, y, t, hk, hT, h0, hj, hkx⟩ :=
    hcr x (min (ε / 2) ρ) (lt_min (by linarith) hρ) (max t1 1) (lt_max_of_lt_right one_pos)
  have hclose : ∀ z, Metric.infDist z A < ε → z ∈ W := by
    intro z hz
    apply interior_subset
    apply hth
    rw [Metric.mem_thickening_iff_infDist_lt hne]
    exact lt_of_lt_of_le hz (min_le_left _ _)
  have hall : ∀ j, j ≤ k → y j ∈ W ∧ (0 < j → Metric.infDist (y j) A < ε) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨interior_subset (hball ?_), fun h => absurd h (lt_irrefl 0)⟩
      rw [Metric.mem_ball]; exact lt_of_lt_of_le h0 (min_le_right _ _)
    | succ i ih =>
      intro hi
      have hyi := (ih (by omega)).1
      have hti : t1 ≤ t i := le_trans (le_max_left _ _) (hT i (by omega))
      have h1 := ht1 (t i) hti (y i) hyi
      have h2 := hj i (by omega)
      have h3 : Metric.infDist (y (i + 1)) A < ε := by
        have := Metric.infDist_le_infDist_add_dist (x := y (i + 1)) (y := ψ (t i) (y i)) (s := A)
        rw [dist_comm] at this
        have h4 : dist (ψ (t i) (y i)) (y (i + 1)) < ε / 2 := lt_of_lt_of_le h2 (min_le_left _ _)
        linarith
      exact ⟨hclose _ h3, fun _ => h3⟩
  have := (hall k le_rfl).2 (by omega)
  rw [hkx] at this
  have : ε ≤ Metric.infDist x A := min_le_right _ _
  linarith

open StochApproxDyn.LimitSet in
theorem chainTo_of_no_attractor {X : Type*} [MetricSpace X] [CompactSpace X] (ψ : Flow ℝ≥0 X)
    (hno : ∀ A : Set X, IsAttractor ψ A → A = Set.univ) : ∀ a b : X, ChainTo ψ a b := by
  intro a b δ hδ T hT
  -- prefixes
  let P : ℕ → (ℕ → X) → (ℕ → ℝ≥0) → Prop := fun k ys ts =>
    (∀ i ≤ k, T ≤ ts i) ∧ dist (ys 0) a < δ ∧ ∀ j < k, dist (ψ (ts j) (ys j)) (ys (j + 1)) < δ
  set U : Set X := {z | ∃ k ys ts, P k ys ts ∧ dist (ψ (ts k) (ys k)) z < δ} with hU
  have hext : ∀ k ys ts w s, P k ys ts → dist (ψ (ts k) (ys k)) w < δ → T ≤ s →
      P (k + 1) (fun i => if i = k + 1 then w else ys i) (fun i => if i = k + 1 then s else ts i) := by
    intro k ys ts w s hP hw hs
    obtain ⟨p1, p2, p3⟩ := hP
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      by_cases h : i = k + 1
      · simp [h, hs]
      · simp only [h, if_false]; exact p1 i (by omega)
    · simpa using p2
    · intro j hj
      by_cases h : j = k
      · subst h; simpa using hw
      · have h1 : j ≠ k + 1 := by omega
        have h2 : j + 1 ≠ k + 1 := by omega
        simp only [h1, h2, if_false]
        exact p3 j (by omega)
  have hUo : IsOpen U := by
    rw [Metric.isOpen_iff]
    rintro z ⟨k, ys, ts, hP, hd⟩
    refine ⟨δ - dist (ψ (ts k) (ys k)) z, by linarith, ?_⟩
    intro w hw
    rw [Metric.mem_ball, dist_comm] at hw
    refine ⟨k, ys, ts, hP, ?_⟩
    have := dist_triangle (ψ (ts k) (ys k)) z w
    linarith
  have hUne : U.Nonempty := by
    refine ⟨ψ T a, 0, fun _ => a, fun _ => T, ⟨fun _ _ => le_rfl, by simpa using hδ, ?_⟩, ?_⟩
    · intro j hj; omega
    · simpa using hδ
  have hTU : ψ T '' closure U ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    have hcont : ContinuousAt (fun x => ψ T x) z := (flow_cont_at ψ T).continuousAt
    obtain ⟨η, hη, hηd⟩ := Metric.continuousAt_iff.mp hcont δ hδ
    obtain ⟨w, hwU, hwz⟩ := Metric.mem_closure_iff.mp hz η hη
    obtain ⟨k, ys, ts, hP, hd⟩ := hwU
    refine ⟨k + 1, fun i => if i = k + 1 then w else ys i,
      fun i => if i = k + 1 then T else ts i, hext k ys ts w T hP hd le_rfl, ?_⟩
    simp only [if_true]
    rw [dist_comm] at hwz
    exact hηd hwz
  obtain ⟨A, hA, hAU, -⟩ := exists_attractor_core ψ U hUo hUne isClosed_closure.isCompact T hT hTU
  have hAu := hno A hA
  have hbU : b ∈ U := hAU (hAu ▸ Set.mem_univ b)
  obtain ⟨k, ys, ts, hP, hd⟩ := hbU
  obtain ⟨p1, p2, p3⟩ := hP
  refine ⟨k + 1, fun i => if i = k + 1 then b else ys i, ts, ⟨by omega, ?_, ?_, ?_, ?_⟩⟩
  · intro i hi; exact p1 i (by omega)
  · simpa using p2
  · intro j hj
    by_cases h : j = k
    · subst h; simpa using hd
    · have h1 : j ≠ k + 1 := by omega
      have h2 : j + 1 ≠ k + 1 := by omega
      simp only [h1, h2, if_false]
      exact p3 j (by omega)
  · simp

theorem tfae_core {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (Λ : Set M) (hΛ : Λ.Nonempty) :
    List.TFAE
      [StochApproxDyn.LimitSet.IsInternallyChainTransitive Φ Λ,
       IsConnected Λ ∧ StochApproxDyn.LimitSet.IsInternallyChainRecurrent Φ Λ,
       IsCompact Λ ∧ ∃ h : StochApproxDyn.LimitSet.IsInvariantSet Φ Λ,
         ∀ A : Set Λ, StochApproxDyn.LimitSet.IsAttractor (StochApproxDyn.LimitSet.restrictSemiflow Φ h) A → A = Set.univ] := by
  tfae_have 1 → 2 := by
    rintro ⟨hne, hc, h, hct⟩
    refine ⟨?_, hne, hc, h, fun p => hct p p⟩
    haveI : CompactSpace Λ := isCompact_iff_compactSpace.mp hc
    have : PreconnectedSpace Λ := ict_preconnected _ hct
    exact ⟨hne, isPreconnected_iff_preconnectedSpace.mpr this⟩
  tfae_have 2 → 3 := by
    rintro ⟨hconn, hne, hc, h, hcr⟩
    refine ⟨hc, h, fun A hA => ?_⟩
    haveI : ConnectedSpace Λ := isConnected_iff_connectedSpace.mp hconn
    have hAo := attractor_isOpen_of_chainRec _ hcr A hA
    exact IsClopen.eq_univ ⟨hA.2.1.isClosed, hAo⟩ hA.1
  tfae_have 3 → 1 := by
    rintro ⟨hc, h, hno⟩
    haveI : CompactSpace Λ := isCompact_iff_compactSpace.mp hc
    exact ⟨hΛ, hc, h, chainTo_of_no_attractor _ hno⟩
  tfae_finish

end StochApproxDyn.Lyapunov

open StochApproxDyn.Lyapunov
open StochApproxDyn.LimitSet

theorem solution {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (Λ : Set M) (hΛ : Λ.Nonempty) :
    List.TFAE
      [IsInternallyChainTransitive Φ Λ,
       IsConnected Λ ∧ IsInternallyChainRecurrent Φ Λ,
       IsCompact Λ ∧ ∃ h : IsInvariantSet Φ Λ,
         ∀ A : Set Λ, IsAttractor (restrictSemiflow Φ h) A → A = Set.univ] := by
  exact tfae_core Φ Λ hΛ
