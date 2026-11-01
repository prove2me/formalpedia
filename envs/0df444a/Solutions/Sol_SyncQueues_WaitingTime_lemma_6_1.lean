-- Prove2me | solution 1 for SyncQueues.WaitingTime.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T14:56:25.450899+00:00
-- url     : https://prove2.me/submissions/5c2f2147-1acf-486c-aeda-1654733ece16

import Mathlib
import Definitions.Def_SyncQueues_WaitingTime_BranchingTree
import Definitions.Def_SyncQueues_WaitingTime_Model
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Theorems.Thm_SyncQueues_WaitingTime_eq_6_3
import Theorems.Thm_SyncQueues_WaitingTime_eq_6_4

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open SyncQueues.WaitingTime

namespace SQL61

section Meas

variable {Ω : Type*} [MeasurableSpace Ω]

lemma meas_sInf_nat {S : Ω → Set ℕ} (hS : ∀ k, MeasurableSet {ω | k ∈ S ω}) :
    Measurable (fun ω => sInf (S ω)) := by
  apply measurable_to_countable'
  intro j
  have hset : (fun ω => sInf (S ω)) ⁻¹' {j} =
      ({ω | j ∈ S ω} ∩ ⋂ k ∈ Finset.range j, {ω | k ∉ S ω}) ∪
        ({ω | j = 0} ∩ ⋂ k, {ω | k ∉ S ω}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range]
    constructor
    · intro h
      by_cases hne : (S ω).Nonempty
      · left
        refine ⟨h ▸ Nat.sInf_mem hne, fun k hk => ?_⟩
        exact Nat.notMem_of_lt_sInf (h ▸ hk)
      · right
        have he : S ω = ∅ := Set.not_nonempty_iff_eq_empty.1 hne
        refine ⟨by rw [← h, he, Nat.sInf_empty], fun k hk => ?_⟩
        rw [he] at hk; exact hk
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · apply le_antisymm (Nat.sInf_le h1)
        by_contra hlt
        push_neg at hlt
        exact h2 _ hlt (Nat.sInf_mem ⟨j, h1⟩)
      · have he : S ω = ∅ := Set.eq_empty_iff_forall_notMem.2 h2
        rw [he, Nat.sInf_empty, h1]
  rw [hset]
  refine (MeasurableSet.inter (hS j) (MeasurableSet.biInter (Set.to_countable _)
    fun k _ => (hS k).compl)).union (MeasurableSet.inter ?_ (MeasurableSet.iInter fun k =>
      (hS k).compl))
  by_cases hj : j = 0
  · simp [hj]
  · simp [hj]

lemma meas_index {ι β : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace β] {K : Ω → ι} (hK : Measurable K) {F : ι → Ω → β}
    (hF : ∀ i, Measurable (F i)) : Measurable (fun ω => F (K ω) ω) := by
  intro s hs
  have : (fun ω => F (K ω) ω) ⁻¹' s = ⋃ i, (K ⁻¹' {i}) ∩ (F i ⁻¹' s) := by
    ext ω; simp
  rw [this]
  exact MeasurableSet.iUnion fun i => (hK (measurableSet_singleton i)).inter (hF i hs)

lemma meas_countable_set {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] {f : Ω → α} (hf : Measurable f) (s : Set α) :
    MeasurableSet (f ⁻¹' s) :=
  hf s.to_countable.measurableSet

variable {m : ℕ} {E : ℕ → Ω → ℝ} {R : ℕ → Ω → (Fin m → ℕ)} {C : ℕ → Ω → (Fin m → ℝ)}

lemma meas_predJob (hR : ∀ k, Measurable (R k)) (k : ℕ) (i : Fin m) :
    Measurable (fun ω => predJob (fun k => R k ω) k i) := by
  unfold predJob
  apply meas_sInf_nat
  intro k'
  have : {ω | k' ∈ {k'' | k < k'' ∧ R k ω i ∈ Set.range (R k'' ω)}} =
      (fun ω => (R k ω, R k' ω)) ⁻¹' {p | k < k' ∧ p.1 i ∈ Set.range p.2} := by
    ext ω; simp
  rw [this]
  exact meas_countable_set ((hR k).prodMk (hR k')) _

lemma meas_predJob' (hR : ∀ k, Measurable (R k)) {K : Ω → ℕ} (hK : Measurable K) (i : Fin m) :
    Measurable (fun ω => predJob (fun k => R k ω) (K ω) i) :=
  meas_index hK (F := fun k ω => predJob (fun k => R k ω) k i) fun k => meas_predJob hR k i

lemma meas_R_at (hR : ∀ k, Measurable (R k)) {K : Ω → ℕ} (hK : Measurable K) :
    Measurable (fun ω => R (K ω) ω) :=
  meas_index hK (F := fun k ω => R k ω) hR

lemma meas_predPiece (hR : ∀ k, Measurable (R k)) (k : ℕ) (i : Fin m) :
    Measurable (fun ω => predPiece (fun k => R k ω) k i) := by
  have h1 : Measurable (fun ω => (R (predJob (fun k => R k ω) k i) ω, R k ω i)) :=
    (meas_R_at hR (meas_predJob hR k i)).prodMk ((measurable_pi_apply i).comp (hR k))
  have h2 := (measurable_of_countable (fun p : (Fin m → ℕ) × ℕ =>
    if h : ∃ i', p.1 i' = p.2 then h.choose else i)).comp h1
  exact h2

lemma meas_arrival (hE : ∀ k, Measurable (E k)) (k : ℕ) :
    Measurable (fun ω => arrival (fun k => E k ω) k) := by
  unfold arrival
  split_ifs
  · exact hE 0
  · exact (Finset.measurable_sum _ fun j _ => hE j).neg

lemma meas_edgeHat (hE : ∀ k, Measurable (E k)) (hR : ∀ k, Measurable (R k))
    (hC : ∀ k, Measurable (C k)) (k : ℕ) (i : Fin m) :
    Measurable (fun ω => edgeHat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) k i) := by
  unfold edgeHat
  have hJ := meas_predJob hR k i
  have hCJ : Measurable (fun ω => C (predJob (fun k => R k ω) k i) ω) :=
    meas_index hJ (F := fun k ω => C k ω) hC
  have hCJP : Measurable (fun ω => C (predJob (fun k => R k ω) k i) ω
      (predPiece (fun k => R k ω) k i)) :=
    meas_index (meas_predPiece hR k i) (F := fun i' ω => C (predJob (fun k => R k ω) k i) ω i')
      (fun i' => (measurable_pi_apply i').comp hCJ)
  have hA : Measurable (fun ω => arrival (fun k => E k ω) (predJob (fun k => R k ω) k i)) :=
    meas_index hJ (F := fun k ω => arrival (fun k => E k ω) k) (meas_arrival hE)
  exact hCJP.sub ((meas_arrival hE k).sub hA)

lemma meas_foldl (hE : ∀ k, Measurable (E k)) (hR : ∀ k, Measurable (R k))
    (hC : ∀ k, Measurable (C k)) (j : List (Fin m)) :
    ∀ st : Ω → ℕ × ℝ, Measurable st →
      Measurable (fun ω => j.foldl (fun (st : ℕ × ℝ) i =>
        (predJob (fun k => R k ω) st.1 i,
          st.2 + edgeHat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) st.1 i)) (st ω)) := by
  induction j with
  | nil => intro st hst; simpa using hst
  | cons i j ih =>
    intro st hst
    simp only [List.foldl_cons]
    apply ih
    refine Measurable.prodMk ?_ ?_
    · exact meas_index hst.fst (F := fun k ω => predJob (fun k => R k ω) k i)
        (fun k => meas_predJob hR k i)
    · exact hst.snd.add (meas_index hst.fst
        (F := fun k ω => edgeHat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) k i)
        (fun k => meas_edgeHat hE hR hC k i))

lemma meas_pathSumHat (hE : ∀ k, Measurable (E k)) (hR : ∀ k, Measurable (R k))
    (hC : ∀ k, Measurable (C k)) (j : List (Fin m)) :
    Measurable (fun ω => pathSumHat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) j) := by
  unfold pathSumHat
  exact (meas_foldl hE hR hC j (fun _ => ((0 : ℕ), (0 : ℝ))) measurable_const).snd

lemma meas_Uhat (hE : ∀ k, Measurable (E k)) (hR : ∀ k, Measurable (R k))
    (hC : ∀ k, Measurable (C k)) (r : ℕ) :
    Measurable (fun ω => Uhat (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) r) := by
  unfold Uhat
  exact Measurable.iSup fun v => meas_pathSumHat hE hR hC _

lemma meas_UhatUpTo (hE : ∀ k, Measurable (E k)) (hR : ∀ k, Measurable (R k))
    (hC : ∀ k, Measurable (C k)) (r : ℕ) :
    Measurable (fun ω => UhatUpTo (fun k => E k ω) (fun k => R k ω) (fun k => C k ω) r) := by
  unfold UhatUpTo
  exact Finset.measurable_range_sup'' fun n _ => meas_Uhat hE hR hC n

lemma meas_Wn (hE : ∀ k, Measurable (E k)) (hR : ∀ k, Measurable (R k))
    (hC : ∀ k, Measurable (C k)) :
    Measurable (fun ω => Wn (fun k => E k ω) (fun k => R k ω) (fun k => C k ω)) := by
  unfold Wn
  exact Measurable.iSup fun r => meas_Uhat hE hR hC r

end Meas

section TreeMeas

variable {m : ℕ} {Ω' : Type*} [MeasurableSpace Ω'] {χ τ : List (Fin m) → Ω' → ℝ}

lemma meas_pathSum (hχ : ∀ j, Measurable (χ j)) (hτ : ∀ j, Measurable (τ j)) (j : List (Fin m)) :
    Measurable (fun ω => pathSum χ τ j ω) := by
  unfold pathSum
  exact Finset.measurable_sum _ fun r _ => (hχ _).sub (hτ _)

lemma meas_genMaxUpTo (hχ : ∀ j, Measurable (χ j)) (hτ : ∀ j, Measurable (τ j)) (k : ℕ) :
    Measurable (fun ω => genMaxUpTo χ τ k ω) := by
  unfold genMaxUpTo genMax
  exact Finset.measurable_range_sup'' fun n _ => Measurable.iSup fun v => meas_pathSum hχ hτ _

lemma meas_endoW (hχ : ∀ j, Measurable (χ j)) (hτ : ∀ j, Measurable (τ j)) :
    Measurable (fun ω => endoW χ τ ω) := by
  unfold endoW
  exact Measurable.iSup fun j => meas_pathSum hχ hτ j


lemma pathSum_nil (ω : Ω') : pathSum χ τ [] ω = 0 := by simp [pathSum]

lemma endoW_nonneg (ω : Ω') : 0 ≤ endoW χ τ ω := by
  unfold endoW
  by_cases h : BddAbove (Set.range fun j => pathSum χ τ j ω)
  · exact (pathSum_nil (χ := χ) (τ := τ) ω).symm.le.trans (le_ciSup h [])
  · rw [Real.iSup_of_not_bddAbove h]

/-- Bound for words of a fixed length by the finite double sum. -/
lemma pathSum_le_sum (ω : Ω') (j : List (Fin m)) {N : ℕ} (hj : j.length < N) :
    pathSum χ τ j ω ≤ ∑ r ∈ Finset.range N, ∑ v : Fin r → Fin m, |pathSum χ τ (List.ofFn v) ω| := by
  have h1 : pathSum χ τ j ω ≤ |pathSum χ τ (List.ofFn j.get) ω| := by
    rw [List.ofFn_get]; exact le_abs_self _
  refine h1.trans ((Finset.single_le_sum (f := fun v : Fin j.length → Fin m =>
    |pathSum χ τ (List.ofFn v) ω|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j.get)).trans ?_)
  exact Finset.single_le_sum (f := fun r => ∑ v : Fin r → Fin m, |pathSum χ τ (List.ofFn v) ω|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_range.2 hj)

end TreeMeas

section Tree

variable {m : ℕ} {lam : ℝ} {Bm : Measure (Fin m → ℝ)} [IsProbabilityMeasure Bm]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {χ τ : List (Fin m) → Ω' → ℝ}

lemma rho_lt_one (hm : 0 < m) (hlam : 0 < lam) {β : ℝ}
    (hint : Integrable (fun x => Real.exp (β * x)) (pieceLaw Bm))
    (hstab : (m : ℝ) * (∫ x, Real.exp (β * x) ∂(pieceLaw Bm)) * (lam * m / (lam * m + β)) < 1)
    (hβ : 0 < β) : rho Bm lam β < 1 := by
  unfold rho
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
  have hq : 0 ≤ lam * m / (lam * m + β) := by
    have : 0 < lam * (m : ℝ) := mul_pos hlam (by exact_mod_cast hm)
    positivity
  have hI : 0 ≤ ∫ x, Real.exp (β * x) ∂(pieceLaw Bm) :=
    integral_nonneg fun x => (Real.exp_pos _).le
  rw [show ((m : ℝ≥0∞)) = ENNReal.ofReal (m : ℝ) by simp,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  exact (ENNReal.ofReal_lt_one).2 hstab

/-- the generation sums `∑_{|j|=r} e^{β S_j}` -/
noncomputable def genExp (χ τ : List (Fin m) → Ω' → ℝ) (β : ℝ) (r : ℕ) (ω : Ω') : ℝ≥0∞ :=
  ∑ v : Fin r → Fin m, ENNReal.ofReal (Real.exp (β * pathSum χ τ (List.ofFn v) ω))

lemma meas_genExp (hχ : ∀ j, Measurable (χ j)) (hτ : ∀ j, Measurable (τ j)) (β : ℝ) (r : ℕ) :
    Measurable (genExp χ τ β r) := by
  unfold genExp
  refine Finset.measurable_sum _ fun v _ => ?_
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((meas_pathSum hχ hτ _).const_mul β))

lemma tree_bdd (hm : 0 < m) (hlam : 0 < lam) (hBm : ∀ᵐ x ∂Bm, ∀ i, 0 ≤ x i)
    (htree : IsLimitTree P' (pieceLaw Bm) (lam * m) χ τ) {β : ℝ} (hβ : 0 < β)
    (hrho : rho Bm lam β < 1) :
    ∀ᵐ ω ∂P', BddAbove (Set.range fun j => pathSum χ τ j ω) := by
  have hχ : ∀ j, Measurable (χ j) := fun j => (htree.1 j).1
  have hτ : ∀ j, Measurable (τ j) := fun j => (htree.1 j).2
  set A : ℕ → Set Ω' := fun r => {ω | ∃ v : Fin r → Fin m, 0 < pathSum χ τ (List.ofFn v) ω}
  have hA : ∀ r, P' (A r) ≤ rho Bm lam β ^ r := by
    intro r
    have h1 : A r ⊆ {ω | 1 ≤ genExp χ τ β r ω} := by
      rintro ω ⟨v, hv⟩
      simp only [Set.mem_setOf_eq, genExp]
      refine le_trans ?_ (Finset.single_le_sum (f := fun v : Fin r → Fin m =>
        ENNReal.ofReal (Real.exp (β * pathSum χ τ (List.ofFn v) ω))) (fun _ _ => zero_le)
        (Finset.mem_univ v))
      rw [ENNReal.one_le_ofReal]
      exact Real.one_le_exp (by positivity)
    calc P' (A r) ≤ P' {ω | 1 ≤ genExp χ τ β r ω} := measure_mono h1
      _ = 1 * P' {ω | 1 ≤ genExp χ τ β r ω} := (one_mul _).symm
      _ ≤ ∫⁻ ω, genExp χ τ β r ω ∂P' :=
          mul_meas_ge_le_lintegral₀ (meas_genExp hχ hτ β r).aemeasurable 1
      _ = rho Bm lam β ^ r := eq_6_4 hm hlam Bm hBm P' χ τ htree hβ r
  have hsum : (∑' r, P' (A r)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hA)
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hrho).ne'
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine ⟨∑ r ∈ Finset.range N, ∑ v : Fin r → Fin m, |pathSum χ τ (List.ofFn v) ω|, ?_⟩
  rintro _ ⟨j, rfl⟩
  by_cases hj : j.length < N
  · exact pathSum_le_sum ω j hj
  · have h := hN j.length (not_lt.1 hj)
    simp only [A, Set.mem_setOf_eq, not_exists, not_lt] at h
    have := h j.get
    rw [List.ofFn_get] at this
    exact this.trans (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- exponential moment of the endogenous solution -/
lemma endoW_expMoment (hm : 0 < m) (hlam : 0 < lam) (hBm : ∀ᵐ x ∂Bm, ∀ i, 0 ≤ x i)
    (htree : IsLimitTree P' (pieceLaw Bm) (lam * m) χ τ) {β : ℝ} (hβ : 0 < β)
    (hrho : rho Bm lam β < 1) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (β * endoW χ τ ω)) ∂P' < ∞ := by
  have hχ : ∀ j, Measurable (χ j) := fun j => (htree.1 j).1
  have hτ : ∀ j, Measurable (τ j) := fun j => (htree.1 j).2
  have hpt : ∀ᵐ ω ∂P', ENNReal.ofReal (Real.exp (β * endoW χ τ ω)) ≤
      ∑' r, genExp χ τ β r ω := by
    filter_upwards [tree_bdd hm hlam hBm htree hβ hrho] with ω hω
    set T := ∑' r, genExp χ τ β r ω with hT
    have hterm : ∀ j : List (Fin m), ENNReal.ofReal (Real.exp (β * pathSum χ τ j ω)) ≤ T := by
      intro j
      have h1 : ENNReal.ofReal (Real.exp (β * pathSum χ τ j ω)) ≤ genExp χ τ β j.length ω := by
        unfold genExp
        conv_lhs => rw [← List.ofFn_get j]
        exact Finset.single_le_sum (f := fun v : Fin j.length → Fin m =>
          ENNReal.ofReal (Real.exp (β * pathSum χ τ (List.ofFn v) ω))) (fun _ _ => zero_le)
          (Finset.mem_univ j.get)
      exact h1.trans (ENNReal.le_tsum (f := fun r => genExp χ τ β r ω) j.length)
    by_cases hTt : T = ∞
    · rw [hTt]; exact le_top
    have hTpos : 0 < T.toReal := by
      have h0 := hterm []
      rw [pathSum_nil, mul_zero, Real.exp_zero, ENNReal.ofReal_one] at h0
      exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le one_pos h0)) hTt
    have hS : ∀ j, pathSum χ τ j ω ≤ Real.log T.toReal / β := by
      intro j
      have h := hterm j
      rw [← ENNReal.ofReal_toReal hTt, ENNReal.ofReal_le_ofReal_iff hTpos.le] at h
      rw [le_div_iff₀ hβ, mul_comm]
      exact (Real.le_log_iff_exp_le hTpos).2 h
    have hW : endoW χ τ ω ≤ Real.log T.toReal / β := ciSup_le hS
    rw [← ENNReal.ofReal_toReal hTt]
    apply ENNReal.ofReal_le_ofReal
    calc Real.exp (β * endoW χ τ ω) ≤ Real.exp (Real.log T.toReal) := by
          apply Real.exp_le_exp.2
          have := mul_le_mul_of_nonneg_left hW hβ.le
          rwa [mul_div_cancel₀ _ hβ.ne'] at this
      _ = T.toReal := Real.exp_log hTpos
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (β * endoW χ τ ω)) ∂P'
      ≤ ∫⁻ ω, ∑' r, genExp χ τ β r ω ∂P' := lintegral_mono_ae hpt
    _ = ∑' r, ∫⁻ ω, genExp χ τ β r ω ∂P' :=
        lintegral_tsum fun r => (meas_genExp hχ hτ β r).aemeasurable
    _ = ∑' r, rho Bm lam β ^ r := by
        congr 1; ext r; exact eq_6_4 hm hlam Bm hBm P' χ τ htree hβ r
    _ < ∞ := by
        rw [ENNReal.tsum_geometric]
        exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt hrho)

end Tree

section Coupling

/-- the optimal transport cost (inside the Wasserstein distance) -/
noncomputable def cpl (q : ℝ) (μ ν : Measure ℝ) : ℝ≥0∞ :=
  ⨅ (π : Measure (ℝ × ℝ)) (_ : π.map Prod.fst = μ ∧ π.map Prod.snd = ν),
    ∫⁻ x : ℝ × ℝ, ENNReal.ofReal (‖x.1 - x.2‖ ^ q) ∂π

lemma wass_eq (p : ℝ) (μ ν : Measure ℝ) :
    WassersteinDRO.Duality.wassersteinDistance p μ ν = cpl p μ ν ^ (1 / p) := rfl

lemma cpl_tendsto_of_wass {p : ℝ} (hp : 0 < p) {μ ν : ℕ → Measure ℝ}
    (h : Tendsto (fun n => WassersteinDRO.Duality.wassersteinDistance p (μ n) (ν n)) atTop (𝓝 0)) :
    Tendsto (fun n => cpl p (μ n) (ν n)) atTop (𝓝 0) := by
  have e : ∀ n, cpl p (μ n) (ν n) = (WassersteinDRO.Duality.wassersteinDistance p (μ n) (ν n)) ^ p := by
    intro n
    rw [wass_eq, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]
  simp_rw [e]
  have := ((ENNReal.continuous_rpow_const (y := p)).tendsto 0).comp h
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hp] using this

lemma cpl_le_of_pair {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (q : ℝ) :
    cpl q (P.map X) (P.map Y) ≤ ∫⁻ ω, ENNReal.ofReal (|X ω - Y ω| ^ q) ∂P := by
  refine iInf₂_le_of_le (P.map (fun ω => (X ω, Y ω))) ⟨?_, ?_⟩ ?_
  · rw [Measure.map_map measurable_fst (hX.prodMk hY)]; rfl
  · rw [Measure.map_map measurable_snd (hX.prodMk hY)]; rfl
  · rw [lintegral_map (by fun_prop) (hX.prodMk hY)]
    simp [Real.norm_eq_abs]

lemma cpl_swap_le (q : ℝ) (μ ν : Measure ℝ) : cpl q ν μ ≤ cpl q μ ν := by
  refine le_iInf₂ fun π hπ => iInf₂_le_of_le (π.map Prod.swap) ⟨?_, ?_⟩ ?_
  · rw [Measure.map_map measurable_fst measurable_swap]; exact hπ.2
  · rw [Measure.map_map measurable_snd measurable_swap]; exact hπ.1
  · rw [lintegral_map (by fun_prop) measurable_swap]
    simp [norm_sub_rev]

lemma cpl_symm (q : ℝ) (μ ν : Measure ℝ) : cpl q μ ν = cpl q ν μ :=
  le_antisymm (cpl_swap_le q ν μ) (cpl_swap_le q μ ν)


end Coupling

lemma tendsto_rpow_zero {c : ℕ → ℝ≥0∞} (hc : Tendsto c atTop (𝓝 0)) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => c n ^ r) atTop (𝓝 0) := by
  have := ((ENNReal.continuous_rpow_const (y := r)).tendsto 0).comp hc
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hr] using this


section Nonneg

variable {m : ℕ} (E : ℕ → ℝ) (R : ℕ → Fin m → ℕ) (C : ℕ → Fin m → ℝ)

lemma Uhat_zero : Uhat E R C 0 = 0 := by
  unfold Uhat
  have : ∀ v : Fin 0 → Fin m, pathSumHat E R C (List.ofFn v) = 0 := by
    intro v; simp [pathSumHat]
  simp only [this, ciSup_const]

lemma Wn_nonneg : 0 ≤ Wn E R C := by
  unfold Wn
  by_cases h : BddAbove (Set.range fun r => Uhat E R C r)
  · exact (Uhat_zero E R C).symm.le.trans (le_ciSup h 0)
  · rw [Real.iSup_of_not_bddAbove h]

lemma UhatUpTo_nonneg (k : ℕ) : 0 ≤ UhatUpTo E R C k := by
  unfold UhatUpTo
  exact (Uhat_zero E R C).symm.le.trans
    (Finset.le_sup' (fun r => Uhat E R C r) (Finset.mem_range.2 (Nat.succ_pos k)))

end Nonneg

lemma rpow_le_exp {p β : ℝ} (hp : 0 < p) (hβ : 0 < β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 ≤ x → x ^ p ≤ K * Real.exp (β * x) := by
  set k : ℕ := ⌈p⌉₊
  refine ⟨1 + (k.factorial : ℝ) / β ^ k, by positivity, fun x hx => ?_⟩
  have h1 : x ^ p ≤ 1 + x ^ k := by
    rcases le_or_gt x 1 with hx1 | hx1
    · have := Real.rpow_le_one hx hx1 hp.le
      have : 0 ≤ x ^ k := pow_nonneg hx k
      linarith
    · have : x ^ p ≤ x ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le (Nat.le_ceil p)
      rw [Real.rpow_natCast] at this
      linarith
  have h2 : x ^ k ≤ (k.factorial : ℝ) / β ^ k * Real.exp (β * x) := by
    have := Real.pow_div_factorial_le_exp (β * x) (mul_nonneg hβ.le hx) k
    rw [mul_pow, div_le_iff₀ (by positivity)] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [pow_pos hβ k, pow_nonneg hx k]
  have h3 : 1 ≤ Real.exp (β * x) := Real.one_le_exp (by positivity)
  nlinarith


/-- tail bound for a bounded-above sequence starting at `0` -/
lemma tail_bound {U : ℕ → ℝ} (hU0 : U 0 = 0) (hb : BddAbove (Set.range U)) {p : ℝ} (hp : 0 < p)
    (k : ℕ) :
    ENNReal.ofReal (|(⨆ r, U r) - (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one U| ^ p) ≤
      ∑' j, ENNReal.ofReal (max (U (j + (k + 1))) 0 ^ p) := by
  set S := ⨆ r, U r
  set Y := (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one U
  set T := ∑' j, ENNReal.ofReal (max (U (j + (k + 1))) 0 ^ p)
  have hYS : Y ≤ S := Finset.sup'_le _ _ fun r _ => le_ciSup hb r
  by_cases hT : T = ∞
  · rw [hT]; exact le_top
  have hterm : ∀ r, k < r → max (U r) 0 ≤ T.toReal ^ (1 / p) := by
    intro r hr
    have h1 : ENNReal.ofReal (max (U r) 0 ^ p) ≤ T := by
      have := ENNReal.le_tsum (f := fun j => ENNReal.ofReal (max (U (j + (k + 1))) 0 ^ p))
        (r - (k + 1))
      rwa [Nat.sub_add_cancel hr] at this
    rw [← ENNReal.ofReal_toReal hT, ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg] at h1
    calc max (U r) 0 = (max (U r) 0 ^ p) ^ (1 / p) := by
          rw [← Real.rpow_mul (le_max_right _ _), mul_one_div_cancel hp.ne', Real.rpow_one]
      _ ≤ T.toReal ^ (1 / p) := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have hY0 : 0 ≤ Y := by
    have := Finset.le_sup' U (Finset.mem_range.2 (Nat.succ_pos k))
    rw [hU0] at this
    exact this
  have hSle : S ≤ Y + T.toReal ^ (1 / p) := by
    apply ciSup_le
    intro r
    have h0 : 0 ≤ T.toReal ^ (1 / p) := by positivity
    by_cases hr : r ≤ k
    · have : U r ≤ Y := Finset.le_sup' U (Finset.mem_range.2 (Nat.lt_succ_of_le hr))
      linarith
    · have h1 := hterm r (not_le.1 hr)
      have h2 := le_max_left (U r) 0
      linarith
  rw [← ENNReal.ofReal_toReal hT]
  apply ENNReal.ofReal_le_ofReal
  rw [abs_of_nonneg (sub_nonneg.2 hYS)]
  calc (S - Y) ^ p ≤ (T.toReal ^ (1 / p)) ^ p :=
        Real.rpow_le_rpow (sub_nonneg.2 hYS) (by linarith) hp.le
    _ = T.toReal := by
        rw [← Real.rpow_mul ENNReal.toReal_nonneg, one_div_mul_cancel hp.ne', Real.rpow_one]

lemma pos_rpow_le_exp {p β : ℝ} (hp : 0 < p) (hβ : 0 < β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, max x 0 ^ p ≤ K * Real.exp (β * x) := by
  obtain ⟨K, hK0, hK⟩ := rpow_le_exp hp hβ
  refine ⟨K, hK0, fun x => ?_⟩
  rcases le_or_gt 0 x with hx | hx
  · rw [max_eq_left hx]; exact hK x hx
  · rw [max_eq_right hx.le, Real.zero_rpow hp.ne']; positivity

lemma max_rpow_le_sum {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) {p β K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ x : ℝ, max x 0 ^ p ≤ K * Real.exp (β * x)) :
    ENNReal.ofReal (max (⨆ i, f i) 0 ^ p) ≤
      ENNReal.ofReal K * ∑ i, ENNReal.ofReal (Real.exp (β * f i)) := by
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := f)
  rw [← hi]
  calc ENNReal.ofReal (max (f i) 0 ^ p) ≤ ENNReal.ofReal K * ENNReal.ofReal (Real.exp (β * f i)) := by
        rw [← ENNReal.ofReal_mul hK0]; exact ENNReal.ofReal_le_ofReal (hK _)
    _ ≤ _ := by
        gcongr
        exact Finset.single_le_sum (f := fun i => ENNReal.ofReal (Real.exp (β * f i)))
          (fun _ _ => zero_le) (Finset.mem_univ i)

lemma tail_tendsto {ρ : ℝ≥0∞} (hρ : ρ < 1) (K : ℝ≥0∞) (hK : K ≠ ∞) :
    Tendsto (fun k : ℕ => K * ∑' j, ρ ^ (j + (k + 1))) atTop (𝓝 0) := by
  have hs : ∑' i, ρ ^ i ≠ ∞ := by
    rw [ENNReal.tsum_geometric]; exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hρ).ne'
  have h1 := (ENNReal.tendsto_sum_nat_add (fun i => ρ ^ i) hs).comp (tendsto_add_atTop_nat 1)
  have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr hK)
  simpa [Function.comp_def] using h2

end SQL61

open SQL61 in
theorem solution {m : ℕ} (hm : 0 < m) {lam : ℝ} (hlam : 0 < lam)
    (Bm : Measure (Fin m → ℝ)) [IsProbabilityMeasure Bm] (hBm : ∀ᵐ x ∂Bm, ∀ i, 0 ≤ x i)
    {β : ℝ} (hβ : 0 < β)
    (hint : Integrable (fun x => Real.exp (β * x)) (pieceLaw Bm))
    (hstab : (m : ℝ) * (∫ x, Real.exp (β * x) ∂(pieceLaw Bm)) * (lam * m / (lam * m + β)) < 1)
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (E : ∀ n, ℕ → Ω n → ℝ) (R : ∀ n, ℕ → Ω n → (Fin m → ℕ)) (C : ∀ n, ℕ → Ω n → (Fin m → ℝ))
    (hsys : ∀ n, m ≤ n → IsSyncSystem (P n) m n lam Bm (E n) (R n) (C n))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (χ τ : List (Fin m) → Ω' → ℝ) (htree : IsLimitTree P' (pieceLaw Bm) (lam * m) χ τ)
    {p : ℝ} (hp : 1 ≤ p) (rn : ℕ → ℕ) (hrn : Tendsto rn atTop atTop) :
    Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal
        (|Wn (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) - UhatUpTo (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) (rn n)| ^ p) ∂(P n)) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal
        (|endoW χ τ ω - genMaxUpTo χ τ (rn n) ω| ^ p) ∂P') atTop (𝓝 0) ∧
    Tendsto (fun n => WassersteinDRO.Duality.wassersteinDistance p
        ((P n).map (fun ω => Wn (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω)))
        ((P n).map (fun ω => UhatUpTo (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) (rn n)))) atTop (𝓝 0) ∧
    Tendsto (fun n => WassersteinDRO.Duality.wassersteinDistance p
        (P'.map (fun ω => genMaxUpTo χ τ (rn n) ω)) (P'.map (fun ω => endoW χ τ ω)))
      atTop (𝓝 0) := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hrho := rho_lt_one hm hlam hint hstab hβ
  have hχ : ∀ j, Measurable (χ j) := fun j => (htree.1 j).1
  have hτ : ∀ j, Measurable (τ j) := fun j => (htree.1 j).2
  obtain ⟨K, hK0, hK⟩ := pos_rpow_le_exp hp0 hβ
  have hMne : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  set g : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal K * ∑' j, rho Bm lam β ^ (j + (k + 1)) with hg
  have hg0 : Tendsto (fun n => g (rn n)) atTop (𝓝 0) :=
    (tail_tendsto hrho _ ENNReal.ofReal_ne_top).comp hrn
  -- the system side
  have hsysb : ∀ n, m ≤ n → ∀ k, ∫⁻ ω, ENNReal.ofReal
      (|Wn (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) -
        UhatUpTo (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) k| ^ p) ∂(P n) ≤ g k := by
    intro n hn k
    have hs := hsys n hn
    have hE : ∀ k, Measurable (E n k) := fun k => (hs.1 k).1
    have hR : ∀ k, Measurable (R n k) := fun k => (hs.1 k).2.1
    have hC : ∀ k, Measurable (C n k) := fun k => (hs.1 k).2.2
    -- Borel–Cantelli: a.s. boundedness
    have hsum : (∑' r, P n {ω | 0 < Uhat (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) r})
        ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun r =>
        ((eq_6_3 hm hlam Bm hBm hn (P n) (E n) (R n) (C n) hs hβ r).1.trans
          (eq_6_3 hm hlam Bm hBm hn (P n) (E n) (R n) (C n) hs hβ r).2))
      rw [ENNReal.tsum_geometric]
      exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hrho).ne'
    have hbdd : ∀ᵐ ω ∂(P n), BddAbove (Set.range fun r =>
        Uhat (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) r) := by
      filter_upwards [ae_eventually_notMem hsum] with ω hω
      obtain ⟨N, hN⟩ := eventually_atTop.1 hω
      refine ⟨∑ r ∈ Finset.range N,
        |Uhat (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) r|, ?_⟩
      rintro _ ⟨r, rfl⟩
      by_cases hr : r < N
      · exact (le_abs_self _).trans (Finset.single_le_sum
          (f := fun r => |Uhat (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) r|)
          (fun _ _ => abs_nonneg _) (Finset.mem_range.2 hr))
      · have h := hN r (not_lt.1 hr)
        simp only [Set.mem_setOf_eq, not_lt] at h
        exact h.trans (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    calc _ ≤ ∫⁻ ω, ∑' j, ENNReal.ofReal (max (Uhat (fun k => E n k ω) (fun k => R n k ω)
            (fun k => C n k ω) (j + (k + 1))) 0 ^ p) ∂(P n) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hbdd] with ω hω
          exact tail_bound (Uhat_zero _ _ _) hω hp0 k
      _ = ∑' j, ∫⁻ ω, ENNReal.ofReal (max (Uhat (fun k => E n k ω) (fun k => R n k ω)
            (fun k => C n k ω) (j + (k + 1))) 0 ^ p) ∂(P n) := by
          refine lintegral_tsum fun j => ?_
          exact (ENNReal.measurable_ofReal.comp
            (((meas_Uhat hE hR hC _).max measurable_const).pow_const p)).aemeasurable
      _ ≤ ∑' j, ENNReal.ofReal K * rho Bm lam β ^ (j + (k + 1)) := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          calc _ ≤ ∫⁻ ω, ENNReal.ofReal K * ∑ v : Fin (j + (k + 1)) → Fin m, ENNReal.ofReal
                (Real.exp (β * pathSumHat (fun k => E n k ω) (fun k => R n k ω)
                  (fun k => C n k ω) (List.ofFn v))) ∂(P n) :=
                lintegral_mono fun ω => max_rpow_le_sum _ hK0 hK
            _ = ENNReal.ofReal K * ∫⁻ ω, ∑ v : Fin (j + (k + 1)) → Fin m, ENNReal.ofReal
                (Real.exp (β * pathSumHat (fun k => E n k ω) (fun k => R n k ω)
                  (fun k => C n k ω) (List.ofFn v))) ∂(P n) := by
                refine lintegral_const_mul _ (Finset.measurable_sum _ fun v _ => ?_)
                exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
                  ((meas_pathSumHat hE hR hC _).const_mul β))
            _ ≤ _ := by
                gcongr
                exact (eq_6_3 hm hlam Bm hBm hn (P n) (E n) (R n) (C n) hs hβ _).2
      _ = g k := by rw [hg, ENNReal.tsum_mul_left]
  -- the tree side
  have htreeb : ∀ k, ∫⁻ ω, ENNReal.ofReal (|endoW χ τ ω - genMaxUpTo χ τ k ω| ^ p) ∂P' ≤ g k := by
    intro k
    calc _ ≤ ∫⁻ ω, ∑' j, ENNReal.ofReal (max (genMax χ τ (j + (k + 1)) ω) 0 ^ p) ∂P' := by
          refine lintegral_mono_ae ?_
          filter_upwards [tree_bdd hm hlam hBm htree hβ hrho] with ω hω
          have hU0 : genMax χ τ 0 ω = 0 := by
            unfold genMax
            have : ∀ v : Fin 0 → Fin m, pathSum χ τ (List.ofFn v) ω = 0 := by
              intro v; simp [pathSum]
            simp only [this, ciSup_const]
          have hb : BddAbove (Set.range fun r => genMax χ τ r ω) := by
            obtain ⟨M, hM⟩ := hω
            refine ⟨M, ?_⟩
            rintro _ ⟨r, rfl⟩
            unfold genMax
            exact ciSup_le fun v => hM ⟨List.ofFn v, rfl⟩
          have hsup : endoW χ τ ω = ⨆ r, genMax χ τ r ω := by
            unfold endoW genMax
            apply le_antisymm
            · apply ciSup_le
              intro j
              refine le_trans ?_ (le_ciSup hb j.length)
              have hb' : BddAbove (Set.range fun v : Fin j.length → Fin m =>
                  pathSum χ τ (List.ofFn v) ω) := (Set.finite_range _).bddAbove
              have := le_ciSup hb' j.get
              simp only [List.ofFn_get] at this
              exact this
            · apply ciSup_le
              intro r
              exact ciSup_le fun v => le_ciSup hω (List.ofFn v)
          have := tail_bound hU0 hb hp0 k
          unfold genMaxUpTo
          rw [hsup]
          exact this
      _ = ∑' j, ∫⁻ ω, ENNReal.ofReal (max (genMax χ τ (j + (k + 1)) ω) 0 ^ p) ∂P' := by
          refine lintegral_tsum fun j => ?_
          refine (ENNReal.measurable_ofReal.comp ((Measurable.max ?_ measurable_const).pow_const
            p)).aemeasurable
          unfold genMax
          exact Measurable.iSup fun v => meas_pathSum hχ hτ _
      _ ≤ ∑' j, ENNReal.ofReal K * rho Bm lam β ^ (j + (k + 1)) := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          calc _ ≤ ∫⁻ ω, ENNReal.ofReal K * ∑ v : Fin (j + (k + 1)) → Fin m, ENNReal.ofReal
                (Real.exp (β * pathSum χ τ (List.ofFn v) ω)) ∂P' :=
                lintegral_mono fun ω => max_rpow_le_sum _ hK0 hK
            _ = ENNReal.ofReal K * ∫⁻ ω, ∑ v : Fin (j + (k + 1)) → Fin m, ENNReal.ofReal
                (Real.exp (β * pathSum χ τ (List.ofFn v) ω)) ∂P' := by
                refine lintegral_const_mul _ (Finset.measurable_sum _ fun v _ => ?_)
                exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
                  ((meas_pathSum hχ hτ _).const_mul β))
            _ = _ := by rw [eq_6_4 hm hlam Bm hBm P' χ τ htree hβ _]
      _ = g k := by rw [hg, ENNReal.tsum_mul_left]
  have T1 : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal
      (|Wn (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) -
        UhatUpTo (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) (rn n)| ^ p) ∂(P n))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg0
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    exact hsysb n hn (rn n)
  have T2 : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal
      (|endoW χ τ ω - genMaxUpTo χ τ (rn n) ω| ^ p) ∂P') atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg0
      (fun _ => zero_le) fun n => htreeb (rn n)
  refine ⟨T1, T2, ?_, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_rpow_zero T1 (by positivity : 0 < 1 / p))
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    have hs := hsys n hn
    have hE : ∀ k, Measurable (E n k) := fun k => (hs.1 k).1
    have hR : ∀ k, Measurable (R n k) := fun k => (hs.1 k).2.1
    have hC : ∀ k, Measurable (C n k) := fun k => (hs.1 k).2.2
    rw [wass_eq]
    exact ENNReal.rpow_le_rpow (cpl_le_of_pair (P n) (meas_Wn hE hR hC)
      (meas_UhatUpTo hE hR hC (rn n)) p) (by positivity)
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_rpow_zero T2 (by positivity : 0 < 1 / p)) (fun _ => zero_le) fun n => ?_
    rw [wass_eq]
    refine ENNReal.rpow_le_rpow ((cpl_le_of_pair P' (meas_genMaxUpTo hχ hτ (rn n))
      (meas_endoW hχ hτ) p).trans (le_of_eq ?_)) (by positivity)
    congr 1; ext ω; rw [abs_sub_comm]
