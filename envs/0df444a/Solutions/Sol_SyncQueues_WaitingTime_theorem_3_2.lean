-- Prove2me | solution 1 for SyncQueues.WaitingTime.theorem_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T14:52:51.445255+00:00
-- url     : https://prove2.me/submissions/8e1b2459-1df2-4861-98ed-e04d67192eb5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SyncQueues_WaitingTime_BranchingTree
import Definitions.Def_SyncQueues_WaitingTime_Model
import Theorems.Thm_SyncQueues_WaitingTime_eq_6_4
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Theorems.Thm_SyncQueues_WaitingTime_theorem_3_2_stability
import Theorems.Thm_SyncQueues_WaitingTime_lemma_6_1
import Theorems.Thm_SyncQueues_WaitingTime_proposition_6_4

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open SyncQueues.WaitingTime

namespace SQMain

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

lemma lintegral_fst {π : Measure (ℝ × ℝ)} {μ : Measure ℝ} (h : π.map Prod.fst = μ)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) : ∫⁻ x, g x ∂μ = ∫⁻ x, g x.1 ∂π := by
  rw [← h, lintegral_map hg measurable_fst]

lemma lintegral_snd {π : Measure (ℝ × ℝ)} {μ : Measure ℝ} (h : π.map Prod.snd = μ)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) : ∫⁻ x, g x ∂μ = ∫⁻ x, g x.2 ∂π := by
  rw [← h, lintegral_map hg measurable_snd]

lemma isProb_of_fst {π : Measure (ℝ × ℝ)} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : π.map Prod.fst = μ) : IsProbabilityMeasure π := by
  constructor
  have := congrArg (fun ν : Measure ℝ => ν Set.univ) h
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ,
    measure_univ] at this
  exact this

/-- moment functional -/
noncomputable def mom (p : ℝ) (μ : Measure ℝ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (|x| ^ p) ∂μ

lemma meas_absrpow (p : ℝ) : Measurable (fun x : ℝ => ENNReal.ofReal (|x| ^ p)) := by
  fun_prop

/-- Minkowski along a coupling (`p ≥ 1`). -/
lemma E2 {p : ℝ} (hp : 1 ≤ p) (μ ν : Measure ℝ) :
    mom p μ ^ (1 / p) ≤ mom p ν ^ (1 / p) + cpl p μ ν ^ (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have key : ∀ π : Measure (ℝ × ℝ), π.map Prod.fst = μ → π.map Prod.snd = ν →
      mom p μ ^ (1 / p) ≤ mom p ν ^ (1 / p) +
        (∫⁻ x : ℝ × ℝ, ENNReal.ofReal (‖x.1 - x.2‖ ^ p) ∂π) ^ (1 / p) := by
    intro π h1 h2
    unfold mom
    rw [lintegral_fst h1 (meas_absrpow p), lintegral_snd h2 (meas_absrpow p)]
    have hpt : ∀ x : ℝ × ℝ, ENNReal.ofReal (|x.1| ^ p) ≤
        ((fun x : ℝ × ℝ => ENNReal.ofReal |x.2|) + (fun x : ℝ × ℝ => ENNReal.ofReal |x.1 - x.2|)) x ^ p := by
      intro x
      simp only [Pi.add_apply]
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le]
      apply ENNReal.ofReal_le_ofReal
      apply Real.rpow_le_rpow (abs_nonneg _) _ hp0.le
      calc |x.1| = |x.2 + (x.1 - x.2)| := by ring_nf
        _ ≤ |x.2| + |x.1 - x.2| := abs_add_le _ _
    calc (∫⁻ x, ENNReal.ofReal (|x.1| ^ p) ∂π) ^ (1 / p)
        ≤ (∫⁻ x, ((fun x : ℝ × ℝ => ENNReal.ofReal |x.2|) +
            (fun x : ℝ × ℝ => ENNReal.ofReal |x.1 - x.2|)) x ^ p ∂π) ^ (1 / p) :=
          ENNReal.rpow_le_rpow (lintegral_mono hpt) (by positivity)
      _ ≤ (∫⁻ x, (ENNReal.ofReal |x.2|) ^ p ∂π) ^ (1 / p) +
            (∫⁻ x, (ENNReal.ofReal |x.1 - x.2|) ^ p ∂π) ^ (1 / p) :=
          ENNReal.lintegral_Lp_add_le (by fun_prop) (by fun_prop) hp
      _ = _ := by
          congr 3
          · ext x; rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
          · ext x; rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le, Real.norm_eq_abs]
  -- pass to the infimum
  have h2 : (mom p μ ^ (1 / p) - mom p ν ^ (1 / p)) ^ p ≤ cpl p μ ν := by
    refine le_iInf₂ fun π hπ => ?_
    have h4 := tsub_le_iff_left.2 (key π hπ.1 hπ.2)
    rw [one_div] at h4
    have h5 := (ENNReal.le_rpow_inv_iff hp0).1 h4
    simpa [one_div] using h5
  have h3 := (ENNReal.le_rpow_inv_iff hp0).2 h2
  rw [← one_div] at h3
  exact tsub_le_iff_left.1 (by simpa [one_div] using h3)

/-- Jensen: `E|d|^s ≤ (E|d|)^s` for `0 < s ≤ 1` on a probability space. -/
lemma jensen_s {π : Measure (ℝ × ℝ)} [IsProbabilityMeasure π] {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (d : ℝ × ℝ → ℝ) (hd : Measurable d) :
    ∫⁻ x, ENNReal.ofReal (|d x| ^ s) ∂π ≤ (∫⁻ x, ENNReal.ofReal |d x| ∂π) ^ s := by
  have h := eLpNorm'_le_eLpNorm'_of_exponent_le hs0 hs1 π hd.aestronglyMeasurable
  simp only [eLpNorm'_eq_lintegral_enorm, Real.enorm_eq_ofReal_abs, ENNReal.rpow_one, div_one] at h
  have h' := ENNReal.rpow_le_rpow h hs0.le
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hs0.ne', ENNReal.rpow_one] at h'
  calc ∫⁻ x, ENNReal.ofReal (|d x| ^ s) ∂π = ∫⁻ x, ENNReal.ofReal |d x| ^ s ∂π := by
        congr 1; ext x; rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hs0.le]
    _ ≤ _ := h'

/-- `0 < s ≤ 1` moment comparison along a coupling. -/
lemma E3 {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (μ ν : Measure ℝ) [IsProbabilityMeasure μ] :
    mom s μ ≤ mom s ν + cpl 1 μ ν ^ s ∧ mom s ν ≤ mom s μ + cpl 1 μ ν ^ s := by
  have hsub : ∀ a b : ℝ, |a| ^ s ≤ |b| ^ s + |a - b| ^ s := by
    intro a b
    calc |a| ^ s ≤ (|b| + |a - b|) ^ s := by
          apply Real.rpow_le_rpow (abs_nonneg _) _ hs0.le
          calc |a| = |b + (a - b)| := by ring_nf
            _ ≤ |b| + |a - b| := abs_add_le _ _
      _ ≤ |b| ^ s + |a - b| ^ s := by
          have := NNReal.rpow_add_le_add_rpow ⟨|b|, abs_nonneg _⟩ ⟨|a - b|, abs_nonneg _⟩ hs0.le hs1
          exact_mod_cast this
  have key : ∀ π : Measure (ℝ × ℝ), π.map Prod.fst = μ → π.map Prod.snd = ν →
      mom s μ ≤ mom s ν + (∫⁻ x : ℝ × ℝ, ENNReal.ofReal (‖x.1 - x.2‖ ^ (1 : ℝ)) ∂π) ^ s ∧
      mom s ν ≤ mom s μ + (∫⁻ x : ℝ × ℝ, ENNReal.ofReal (‖x.1 - x.2‖ ^ (1 : ℝ)) ∂π) ^ s := by
    intro π h1 h2
    haveI := isProb_of_fst (μ := μ) h1
    have hJ := jensen_s (π := π) hs0 hs1 (fun x : ℝ × ℝ => x.1 - x.2) (by fun_prop)
    simp only [Real.rpow_one, Real.norm_eq_abs]
    unfold mom
    rw [lintegral_fst h1 (meas_absrpow s), lintegral_snd h2 (meas_absrpow s)]
    constructor
    · calc ∫⁻ x, ENNReal.ofReal (|x.1| ^ s) ∂π
          ≤ ∫⁻ x, (ENNReal.ofReal (|x.2| ^ s) + ENNReal.ofReal (|x.1 - x.2| ^ s)) ∂π := by
            refine lintegral_mono fun x => ?_
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            exact ENNReal.ofReal_le_ofReal (hsub _ _)
        _ = ∫⁻ x, ENNReal.ofReal (|x.2| ^ s) ∂π + ∫⁻ x, ENNReal.ofReal (|x.1 - x.2| ^ s) ∂π :=
            lintegral_add_left (by fun_prop) _
        _ ≤ _ := add_le_add le_rfl hJ
    · calc ∫⁻ x, ENNReal.ofReal (|x.2| ^ s) ∂π
          ≤ ∫⁻ x, (ENNReal.ofReal (|x.1| ^ s) + ENNReal.ofReal (|x.1 - x.2| ^ s)) ∂π := by
            refine lintegral_mono fun x => ?_
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            refine ENNReal.ofReal_le_ofReal ((hsub x.2 x.1).trans_eq ?_)
            rw [abs_sub_comm]
        _ = ∫⁻ x, ENNReal.ofReal (|x.1| ^ s) ∂π + ∫⁻ x, ENNReal.ofReal (|x.1 - x.2| ^ s) ∂π :=
            lintegral_add_left (by fun_prop) _
        _ ≤ _ := add_le_add le_rfl hJ
  have hinf : ∀ (a b : ℝ≥0∞), (∀ π : Measure (ℝ × ℝ), π.map Prod.fst = μ → π.map Prod.snd = ν →
      a ≤ b + (∫⁻ x : ℝ × ℝ, ENNReal.ofReal (‖x.1 - x.2‖ ^ (1 : ℝ)) ∂π) ^ s) →
      a ≤ b + cpl 1 μ ν ^ s := by
    intro a b h
    have h2 : (a - b) ^ s⁻¹ ≤ cpl 1 μ ν := by
      refine le_iInf₂ fun π hπ => ?_
      exact (ENNReal.rpow_inv_le_iff hs0).2 (tsub_le_iff_left.2 (h π hπ.1 hπ.2))
    have h3 := (ENNReal.rpow_inv_le_iff hs0).1 h2
    exact tsub_le_iff_left.1 h3
  exact ⟨hinf _ _ fun π h1 h2 => (key π h1 h2).1, hinf _ _ fun π h1 h2 => (key π h1 h2).2⟩

/-- Lipschitz test functions along a coupling. -/
lemma E1 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] {F : ℝ → ℝ} {C : ℝ}
    (hFb : ∀ x y, dist (F x) (F y) ≤ C) {L : NNReal} (hL : LipschitzWith L F) :
    ENNReal.ofReal |∫ x, F x ∂μ - ∫ x, F x ∂ν| ≤ ((L : ℝ≥0∞) + 1) * cpl 1 μ ν := by
  have hc0 : ((L : ℝ≥0∞) + 1) ≠ 0 := by simp
  have hct : ((L : ℝ≥0∞) + 1) ≠ ∞ := by simp
  unfold cpl
  simp_rw [ENNReal.mul_iInf_of_ne hc0 hct]
  refine le_iInf₂ fun π hπ => ?_
  haveI := isProb_of_fst (μ := μ) hπ.1
  have hFc : Continuous F := hL.continuous
  have hbd : ∀ x, |F x| ≤ |F 0| + C := by
    intro x
    have := hFb x 0
    rw [Real.dist_eq] at this
    have := abs_sub_abs_le_abs_sub (F x) (F 0)
    linarith
  have hi1 : Integrable (fun x : ℝ × ℝ => F x.1) π :=
    Integrable.of_bound (by fun_prop) (|F 0| + C) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hbd _)
  have hi2 : Integrable (fun x : ℝ × ℝ => F x.2) π :=
    Integrable.of_bound (by fun_prop) (|F 0| + C) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hbd _)
  rw [← hπ.1, ← hπ.2, integral_map measurable_fst.aemeasurable hFc.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable hFc.aestronglyMeasurable, ← integral_sub hi1 hi2]
  calc ENNReal.ofReal |∫ x, (F x.1 - F x.2) ∂π|
      = ‖∫ x, (F x.1 - F x.2) ∂π‖ₑ := (Real.enorm_eq_ofReal_abs _).symm
    _ ≤ ∫⁻ x, ‖F x.1 - F x.2‖ₑ ∂π := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, ((L : ℝ≥0∞) + 1) * ENNReal.ofReal (‖x.1 - x.2‖ ^ (1 : ℝ)) ∂π := by
        refine lintegral_mono fun x => ?_
        rw [Real.rpow_one, ← edist_eq_enorm_sub, ← dist_eq_norm, ← edist_dist]
        calc edist (F x.1) (F x.2) ≤ L * edist x.1 x.2 := hL x.1 x.2
          _ ≤ ((L : ℝ≥0∞) + 1) * edist x.1 x.2 := by gcongr; exact le_self_add
    _ = ((L : ℝ≥0∞) + 1) * ∫⁻ x, ENNReal.ofReal (‖x.1 - x.2‖ ^ (1 : ℝ)) ∂π :=
        lintegral_const_mul _ (by fun_prop)

end Coupling

section Chain

lemma ennreal_squeeze {u e : ℕ → ℝ≥0∞} {v : ℝ≥0∞} (hv : v ≠ ∞) (he : Tendsto e atTop (𝓝 0))
    (h1 : ∀ n, u n ≤ v + e n) (h2 : ∀ n, v ≤ u n + e n) :
    Tendsto u atTop (𝓝 v) := by
  have hlo : Tendsto (fun n => v - e n) atTop (𝓝 (v - 0)) :=
    ENNReal.Tendsto.sub tendsto_const_nhds he (Or.inl hv)
  have hhi : Tendsto (fun n => v + e n) atTop (𝓝 (v + 0)) := tendsto_const_nhds.add he
  rw [tsub_zero] at hlo
  rw [add_zero] at hhi
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
    (fun n => tsub_le_iff_right.2 (h2 n)) h1

lemma tendsto_rpow_zero {c : ℕ → ℝ≥0∞} (hc : Tendsto c atTop (𝓝 0)) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => c n ^ r) atTop (𝓝 0) := by
  have := ((ENNReal.continuous_rpow_const (y := r)).tendsto 0).comp hc
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hr] using this

lemma three_le {x1 x2 x3 x4 e1 e2 e3 : ℝ≥0∞} (h1 : x1 ≤ x2 + e1) (h2 : x2 ≤ x3 + e2)
    (h3 : x3 ≤ x4 + e3) : x1 ≤ x4 + (e1 + e2 + e3) := by
  calc x1 ≤ x2 + e1 := h1
    _ ≤ (x3 + e2) + e1 := add_le_add h2 le_rfl
    _ ≤ ((x4 + e3) + e2) + e1 := add_le_add (add_le_add h3 le_rfl) le_rfl
    _ = x4 + (e1 + e2 + e3) := by ring

lemma chain {μ a b : ℕ → Measure ℝ} {ν : Measure ℝ} [hμ : ∀ n, IsProbabilityMeasure (μ n)]
    [IsProbabilityMeasure ν] [hb : ∀ n, IsProbabilityMeasure (b n)]
    (h1 : ∀ q, 1 ≤ q → Tendsto (fun n => cpl q (μ n) (a n)) atTop (𝓝 0))
    (h2 : ∀ q, 1 ≤ q → Tendsto (fun n => cpl q (a n) (b n)) atTop (𝓝 0))
    (h3 : ∀ q, 1 ≤ q → Tendsto (fun n => cpl q (b n) ν) atTop (𝓝 0)) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun n => ⟨μ n, hμ n⟩) atTop
        (𝓝 ⟨ν, inferInstance⟩) ∧
      ∀ p : ℝ, 0 < p → mom p ν ≠ ∞ → Tendsto (fun n => mom p (μ n)) atTop (𝓝 (mom p ν)) := by
  constructor
  · refine tendsto_iff_forall_lipschitz_integral_tendsto.2 ?_
    rintro F ⟨C, hC⟩ ⟨L, hL⟩
    simp only [ProbabilityMeasure.coe_mk]
    set c : ℝ≥0∞ := (L : ℝ≥0∞) + 1
    set B : ℕ → ℝ≥0∞ := fun n => c * (cpl 1 (μ n) (a n) + cpl 1 (b n) (a n) + cpl 1 (b n) ν)
    have hB : Tendsto B atTop (𝓝 0) := by
      have : Tendsto (fun n => cpl 1 (μ n) (a n) + cpl 1 (b n) (a n) + cpl 1 (b n) ν) atTop
          (𝓝 (0 + 0 + 0)) := by
        refine ((h1 1 le_rfl).add ?_).add (h3 1 le_rfl)
        simp_rw [cpl_symm 1 (b _) (a _)]
        exact h2 1 le_rfl
      rw [add_zero, add_zero] at this
      have := ENNReal.Tendsto.const_mul (a := c) this (Or.inr (by simp [c]))
      simpa [B] using this
    have hle : ∀ n, ENNReal.ofReal |∫ x, F x ∂(μ n) - ∫ x, F x ∂ν| ≤ B n := by
      intro n
      have e1 := E1 (μ n) (a n) hC hL
      have e2 := E1 (b n) (a n) hC hL
      have e3 := E1 (b n) ν hC hL
      rw [abs_sub_comm] at e2
      calc ENNReal.ofReal |∫ x, F x ∂(μ n) - ∫ x, F x ∂ν|
          ≤ ENNReal.ofReal (|∫ x, F x ∂(μ n) - ∫ x, F x ∂(a n)| +
              |∫ x, F x ∂(a n) - ∫ x, F x ∂(b n)| + |∫ x, F x ∂(b n) - ∫ x, F x ∂ν|) := by
            apply ENNReal.ofReal_le_ofReal
            calc _ ≤ |∫ x, F x ∂(μ n) - ∫ x, F x ∂(b n)| + |∫ x, F x ∂(b n) - ∫ x, F x ∂ν| :=
                  abs_sub_le _ _ _
              _ ≤ _ := by gcongr; exact abs_sub_le _ _ _
        _ ≤ ENNReal.ofReal |∫ x, F x ∂(μ n) - ∫ x, F x ∂(a n)| +
              ENNReal.ofReal |∫ x, F x ∂(a n) - ∫ x, F x ∂(b n)| +
              ENNReal.ofReal |∫ x, F x ∂(b n) - ∫ x, F x ∂ν| := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_add (by positivity) (by positivity)]
        _ ≤ c * cpl 1 (μ n) (a n) + c * cpl 1 (b n) (a n) + c * cpl 1 (b n) ν := by
            gcongr
        _ = B n := by simp only [B]; ring
    have hd : Tendsto (fun n => ENNReal.ofReal |∫ x, F x ∂(μ n) - ∫ x, F x ∂ν|) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hB (fun _ => zero_le) hle
    have hd' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hd
    simp only [Function.comp_def, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_zero] at hd'
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq] using hd'
  · intro p hp hfin
    rcases le_or_gt 1 p with hp1 | hp1
    · -- Minkowski
      set N : Measure ℝ → ℝ≥0∞ := fun μ => mom p μ ^ (1 / p)
      have hp0 : 0 < 1 / p := by positivity
      set e : ℕ → ℝ≥0∞ := fun n => cpl p (μ n) (a n) ^ (1 / p) + cpl p (a n) (b n) ^ (1 / p) +
        cpl p (b n) ν ^ (1 / p)
      have he : Tendsto e atTop (𝓝 0) := by
        have := ((tendsto_rpow_zero (h1 p hp1) hp0).add (tendsto_rpow_zero (h2 p hp1) hp0)).add
          (tendsto_rpow_zero (h3 p hp1) hp0)
        simpa [e, one_div] using this
      have hup : ∀ n, N (μ n) ≤ N ν + e n := fun n =>
        three_le (E2 hp1 (μ n) (a n)) (E2 hp1 (a n) (b n)) (E2 hp1 (b n) ν)
      have hdn : ∀ n, N ν ≤ N (μ n) + e n := by
        intro n
        have k1 := E2 hp1 (a n) (μ n)
        have k2 := E2 hp1 (b n) (a n)
        have k3 := E2 hp1 ν (b n)
        rw [cpl_symm] at k1 k2 k3
        have := three_le k3 k2 k1
        simpa [N, e, one_div, add_comm, add_left_comm, add_assoc] using this
      have hNfin : N ν ≠ ∞ := by
        simp only [N]
        exact ENNReal.rpow_ne_top_of_nonneg hp0.le hfin
      have hN := ennreal_squeeze hNfin he hup hdn
      have hmom : ∀ μ : Measure ℝ, mom p μ = N μ ^ p := by
        intro μ
        simp only [N]
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (by positivity), ENNReal.rpow_one]
      simp_rw [hmom]
      exact ((ENNReal.continuous_rpow_const (y := p)).tendsto _).comp hN
    · -- `p < 1`
      set e : ℕ → ℝ≥0∞ := fun n => cpl 1 (μ n) (a n) ^ p + cpl 1 (b n) (a n) ^ p +
        cpl 1 (b n) ν ^ p
      have he : Tendsto e atTop (𝓝 0) := by
        have h2' : Tendsto (fun n => cpl 1 (b n) (a n)) atTop (𝓝 0) := by
          simp_rw [cpl_symm 1 (b _) (a _)]; exact h2 1 le_rfl
        have := ((tendsto_rpow_zero (h1 1 le_rfl) hp).add (tendsto_rpow_zero h2' hp)).add
          (tendsto_rpow_zero (h3 1 le_rfl) hp)
        simpa [e] using this
      have hup : ∀ n, mom p (μ n) ≤ mom p ν + e n := fun n =>
        three_le (E3 hp hp1.le (μ n) (a n)).1 (E3 hp hp1.le (b n) (a n)).2
          (E3 hp hp1.le (b n) ν).1
      have hdn : ∀ n, mom p ν ≤ mom p (μ n) + e n := by
        intro n
        have := three_le (E3 hp hp1.le (b n) ν).2 (E3 hp hp1.le (b n) (a n)).1
          (E3 hp hp1.le (μ n) (a n)).2
        simpa [e, add_comm, add_left_comm, add_assoc] using this
      exact ennreal_squeeze hfin he hup hdn

end Chain

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

section TreeMom

variable {m : ℕ} {lam : ℝ} {Bm : Measure (Fin m → ℝ)} [IsProbabilityMeasure Bm]
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {χ τ : List (Fin m) → Ω' → ℝ}

lemma endoW_rpow_lt_top (hm : 0 < m) (hlam : 0 < lam) (hBm : ∀ᵐ x ∂Bm, ∀ i, 0 ≤ x i)
    (htree : IsLimitTree P' (pieceLaw Bm) (lam * m) χ τ) {β : ℝ} (hβ : 0 < β)
    (hrho : rho Bm lam β < 1) {p : ℝ} (hp : 0 < p) :
    ∫⁻ ω, ENNReal.ofReal (endoW χ τ ω ^ p) ∂P' < ∞ := by
  obtain ⟨K, hK0, hK⟩ := rpow_le_exp hp hβ
  calc ∫⁻ ω, ENNReal.ofReal (endoW χ τ ω ^ p) ∂P'
      ≤ ∫⁻ ω, ENNReal.ofReal K * ENNReal.ofReal (Real.exp (β * endoW χ τ ω)) ∂P' := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_mul hK0]
        exact ENNReal.ofReal_le_ofReal (hK _ (endoW_nonneg ω))
    _ = ENNReal.ofReal K * ∫⁻ ω, ENNReal.ofReal (Real.exp (β * endoW χ τ ω)) ∂P' := by
        have hχ : ∀ j, Measurable (χ j) := fun j => (htree.1 j).1
        have hτ : ∀ j, Measurable (τ j) := fun j => (htree.1 j).2
        exact lintegral_const_mul _ (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          ((meas_endoW hχ hτ).const_mul β)))
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (endoW_expMoment hm hlam hBm htree hβ hrho)

end TreeMom

lemma mom_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {X : Ω → ℝ} (hX : Measurable X)
    (h0 : ∀ ω, 0 ≤ X ω) (p : ℝ) :
    mom p (P.map X) = ∫⁻ ω, ENNReal.ofReal (X ω ^ p) ∂P := by
  unfold mom
  rw [lintegral_map (meas_absrpow p) hX]
  congr 1; ext ω; rw [abs_of_nonneg (h0 ω)]

end SQMain

open SQMain in
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
    (χ τ : List (Fin m) → Ω' → ℝ) (htree : IsLimitTree P' (pieceLaw Bm) (lam * m) χ τ) :
    ∃ W : ∀ n, Ω n → ℝ,
      (∀ n, m ≤ n → ∀ᵐ ω ∂(P n),
        Tendsto (fun t0 => waitT (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) t0) atBot (𝓝 (W n ω))) ∧
      (∀ᵐ ω ∂P', BddAbove (Set.range fun j => pathSum χ τ j ω)) ∧
      TendstoInDistribution W atTop (endoW χ τ) P P' ∧
      ∀ p : ℝ, 0 < p →
        Integrable (fun ω => endoW χ τ ω ^ p) P' ∧
        (∀ᶠ n in atTop, Integrable (fun ω => W n ω ^ p) (P n)) ∧
        Tendsto (fun n => ∫ ω, W n ω ^ p ∂(P n)) atTop
          (𝓝 (∫ ω, endoW χ τ ω ^ p ∂P')) := by
  classical
  have hrho := rho_lt_one hm hlam hint hstab hβ
  have hχ : ∀ j, Measurable (χ j) := fun j => (htree.1 j).1
  have hτ : ∀ j, Measurable (τ j) := fun j => (htree.1 j).2
  -- the stationary waiting times (junk value `0` when `n < m`, where no system exists)
  set W : ∀ n, Ω n → ℝ := fun n ω =>
    if m ≤ n then Wn (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) else 0 with hWdef
  set Y : ∀ n, Ω n → ℝ := fun n ω =>
    if m ≤ n then UhatUpTo (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) n else 0
    with hYdef
  have hWm : ∀ n, Measurable (W n) := by
    intro n
    by_cases h : m ≤ n
    · have hs := (hsys n h).1
      simp only [hWdef, if_pos h]
      exact meas_Wn (fun k => (hs k).1) (fun k => (hs k).2.1) (fun k => (hs k).2.2)
    · simp only [hWdef, if_neg h]; exact measurable_const
  have hYm : ∀ n, Measurable (Y n) := by
    intro n
    by_cases h : m ≤ n
    · have hs := (hsys n h).1
      simp only [hYdef, if_pos h]
      exact meas_UhatUpTo (fun k => (hs k).1) (fun k => (hs k).2.1) (fun k => (hs k).2.2) n
    · simp only [hYdef, if_neg h]; exact measurable_const
  have hW0 : ∀ n ω, 0 ≤ W n ω := by
    intro n ω
    simp only [hWdef]
    split_ifs
    · exact Wn_nonneg _ _ _
    · exact le_rfl
  have hGm : ∀ k, Measurable (fun ω => genMaxUpTo χ τ k ω) := meas_genMaxUpTo hχ hτ
  have hZm : Measurable (fun ω => endoW χ τ ω) := meas_endoW hχ hτ
  refine ⟨W, ?_, tree_bdd hm hlam hBm htree hβ hrho, ?_⟩
  · -- (1) stability, for every `n ≥ m`
    intro n hn
    filter_upwards [theorem_3_2_stability hm hlam Bm hBm hβ hint hstab hn (P n) (E n) (R n) (C n)
      (hsys n hn)] with ω hω
    simp only [hWdef, if_pos hn]
    exact hω.2
  -- the chain of couplings (6.5)
  haveI hμ : ∀ n, IsProbabilityMeasure ((P n).map (W n)) := fun n =>
    Measure.isProbabilityMeasure_map (hWm n).aemeasurable
  haveI hb : ∀ n, IsProbabilityMeasure (P'.map (fun ω => genMaxUpTo χ τ n ω)) := fun n =>
    Measure.isProbabilityMeasure_map (hGm n).aemeasurable
  haveI : IsProbabilityMeasure (P'.map (fun ω => endoW χ τ ω)) :=
    Measure.isProbabilityMeasure_map hZm.aemeasurable
  have h1 : ∀ q : ℝ, 1 ≤ q → Tendsto (fun n => cpl q ((P n).map (W n)) ((P n).map (Y n)))
      atTop (𝓝 0) := by
    intro q hq
    have L := (lemma_6_1 hm hlam Bm hBm hβ hint hstab Ω P E R C hsys P' χ τ htree hq
      (fun n => n) tendsto_id).1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds L
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    refine (cpl_le_of_pair (P n) (hWm n) (hYm n) q).trans (le_of_eq ?_)
    simp only [hWdef, hYdef, if_pos hn]
  have h2 : ∀ q : ℝ, 1 ≤ q → Tendsto (fun n => cpl q ((P n).map (Y n))
      (P'.map (fun ω => genMaxUpTo χ τ n ω))) atTop (𝓝 0) := by
    intro q hq
    have L := proposition_6_4 hm hlam Bm hBm hβ hint hstab Ω P E R C hsys P' χ τ htree hq
      (fun n => n) tendsto_id
    have L' := cpl_tendsto_of_wass (lt_of_lt_of_le one_pos hq) L
    refine L'.congr' ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    have : Y n = fun ω => UhatUpTo (fun k => E n k ω) (fun k => R n k ω) (fun k => C n k ω) n := by
      funext ω; simp only [hYdef, if_pos hn]
    rw [this]
  have h3 : ∀ q : ℝ, 1 ≤ q → Tendsto (fun n => cpl q (P'.map (fun ω => genMaxUpTo χ τ n ω))
      (P'.map (fun ω => endoW χ τ ω))) atTop (𝓝 0) := by
    intro q hq
    have L := (lemma_6_1 hm hlam Bm hBm hβ hint hstab Ω P E R C hsys P' χ τ htree hq
      (fun n => n) tendsto_id).2.1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds L
      (fun _ => zero_le) fun n => ?_
    refine (cpl_le_of_pair P' (hGm n) hZm q).trans (le_of_eq ?_)
    congr 1; ext ω; rw [abs_sub_comm]
  obtain ⟨hD, hM⟩ := chain (μ := fun n => (P n).map (W n)) (a := fun n => (P n).map (Y n))
    (b := fun n => P'.map (fun ω => genMaxUpTo χ τ n ω)) (ν := P'.map (fun ω => endoW χ τ ω))
    h1 h2 h3
  refine ⟨⟨fun n => (hWm n).aemeasurable, hZm.aemeasurable, hD⟩, fun p hp => ?_⟩
  -- (4) moments
  have hZfin := endoW_rpow_lt_top hm hlam hBm htree hβ hrho hp
  have hνmom : mom p (P'.map (fun ω => endoW χ τ ω)) = ∫⁻ ω, ENNReal.ofReal (endoW χ τ ω ^ p) ∂P' :=
    mom_map P' hZm endoW_nonneg p
  have hμmom : ∀ n, mom p ((P n).map (W n)) = ∫⁻ ω, ENNReal.ofReal (W n ω ^ p) ∂(P n) :=
    fun n => mom_map (P n) (hWm n) (hW0 n) p
  have hT := hM p hp (by rw [hνmom]; exact hZfin.ne)
  simp only [hμmom, hνmom] at hT
  have hZint : Integrable (fun ω => endoW χ τ ω ^ p) P' :=
    ⟨(hZm.pow_const p).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun ω => Real.rpow_nonneg (endoW_nonneg ω) p)).2 hZfin⟩
  refine ⟨hZint, ?_, ?_⟩
  · filter_upwards [hT.eventually_lt_const hZfin] with n hn
    exact ⟨((hWm n).pow_const p).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun ω => Real.rpow_nonneg (hW0 n ω) p)).2 hn⟩
  · have e1 : ∀ n, ∫ ω, W n ω ^ p ∂(P n) = (∫⁻ ω, ENNReal.ofReal (W n ω ^ p) ∂(P n)).toReal :=
      fun n => integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun ω => Real.rpow_nonneg (hW0 n ω) p)
        ((hWm n).pow_const p).aestronglyMeasurable
    have e2 : ∫ ω, endoW χ τ ω ^ p ∂P' = (∫⁻ ω, ENNReal.ofReal (endoW χ τ ω ^ p) ∂P').toReal :=
      integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun ω => Real.rpow_nonneg (endoW_nonneg ω) p)
        (hZm.pow_const p).aestronglyMeasurable
    simp only [e1, e2]
    exact (ENNReal.tendsto_toReal hZfin.ne).comp hT

