-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P24.zeroParametersHSW
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T07:22:40.828342+00:00
-- url     : https://prove2.me/submissions/e6342e4b-5a55-4693-884d-520d56c1c483

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P24


/-! Attainment of Holevo-type maxima over finite ensembles of density matrices
(Carathéodory reduction to a fixed ensemble size, then compactness). -/

open scoped ComplexOrder Matrix
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6AT

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- density matrices. -/
def Dens (I : Type*) [Fintype I] : Set (Matrix I I ℂ) := {ρ | ρ.PosSemidef ∧ ρ.trace = 1}

lemma isClosed_psd : IsClosed {P : Matrix I I ℂ | P.PosSemidef} := by
  have : {P : Matrix I I ℂ | P.PosSemidef} =
      {P | Pᴴ = P} ∩ ⋂ x : I → ℂ, {P | 0 ≤ star x ⬝ᵥ (P *ᵥ x)} := by
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec]
    rfl
  rw [this]
  refine IsClosed.inter (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
    (isClosed_iInter fun x => isClosed_le continuous_const ?_)
  exact continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

lemma psd_decomp (A : Matrix I I ℂ) (hA : A.PosSemidef) :
    ∃ B : Matrix I I ℂ, A = Bᴴ * B := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  open scoped MatrixOrder in
  have hB : (CFC.sqrt A).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  open scoped MatrixOrder in
  have hAB : A = (CFC.sqrt A)ᴴ * CFC.sqrt A := by
    rw [hB.isHermitian.eq, CFC.sqrt_mul_sqrt_self A h0]
  exact ⟨_, hAB⟩

lemma entry_bound (A : Matrix I I ℂ) (hA : A.PosSemidef) (i j : I) :
    ‖A i j‖ ≤ 2 * (A.trace).re := by
  obtain ⟨B, rfl⟩ := psd_decomp A hA
  have hij : (Bᴴ * B) i j = ∑ k, star (B k i) * B k j := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have htr : ((Bᴴ * B).trace).re = ∑ l, ∑ k, ‖B k l‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    norm_cast
  rw [hij, htr, Finset.sum_comm]
  calc ‖∑ k, star (B k i) * B k j‖ ≤ ∑ k, ‖star (B k i) * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ k, (‖B k i‖ ^ 2 + ‖B k j‖ ^ 2) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_star]
        nlinarith [sq_nonneg (‖B k i‖ - ‖B k j‖), norm_nonneg (B k i), norm_nonneg (B k j)]
    _ ≤ ∑ k, (∑ l, ‖B k l‖ ^ 2 + ∑ l, ‖B k l‖ ^ 2) := by
        refine Finset.sum_le_sum fun k _ => add_le_add ?_ ?_
        · exact Finset.single_le_sum (f := fun l => ‖B k l‖ ^ 2)
            (fun l _ => sq_nonneg _) (Finset.mem_univ i)
        · exact Finset.single_le_sum (f := fun l => ‖B k l‖ ^ 2)
            (fun l _ => sq_nonneg _) (Finset.mem_univ j)
    _ = 2 * ∑ k, ∑ l, ‖B k l‖ ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring

lemma dens_compact : IsCompact (Dens I) := by
  let Bs : Set (Matrix I I ℂ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) 2
  have hBs : IsCompact Bs :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hc : IsClosed (Dens I) :=
    isClosed_psd.inter (isClosed_eq (continuous_id.matrix_trace) continuous_const)
  refine hBs.of_isClosed_subset hc fun ρ hρ => ?_
  simp only [Bs, Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  intro i _ j _
  rw [Metric.mem_closedBall, dist_zero_right]
  have := entry_bound ρ hρ.1 i j
  rw [hρ.2] at this; simpa using this

lemma dens_avg {k : ℕ} (p : Fin k → ℝ) (ρ : Fin k → Matrix I I ℂ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (hρ : ∀ i, ρ i ∈ Dens I) : ∑ i, p i • ρ i ∈ Dens I := by
  constructor
  · refine Matrix.posSemidef_sum _ fun i _ => ?_
    have := (hρ i).1.smul (show (0 : ℂ) ≤ (p i : ℂ) by exact_mod_cast hp i)
    rwa [Complex.coe_smul] at this
  · rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul, (hρ _).2]
    simp only [Complex.real_smul, mul_one]
    exact_mod_cast hp1

/-- the fixed ensemble size supplied by Carathéodory's theorem. -/
abbrev KK (I : Type*) [Fintype I] : ℕ := Module.finrank ℝ (Matrix I I ℂ × ℝ) + 1

lemma red [Nonempty I] (h : Matrix I I ℂ → ℝ) {k : ℕ} (p : Fin k → ℝ) (ρ : Fin k → Matrix I I ℂ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (hρ : ∀ i, ρ i ∈ Dens I) :
    ∃ (q : Fin (KK I) → ℝ) (σ : Fin (KK I) → Matrix I I ℂ), (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧
      (∀ i, σ i ∈ Dens I) ∧ ∑ i, q i • σ i = ∑ i, p i • ρ i ∧
      ∑ i, q i * h (σ i) = ∑ i, p i * h (ρ i) := by
  set S : Set (Matrix I I ℂ × ℝ) := {z | ∃ r ∈ Dens I, z = (r, h r)}
  have hx : ∑ i, p i • ((ρ i, h (ρ i)) : Matrix I I ℂ × ℝ) ∈ convexHull ℝ S :=
    (convex_convexHull ℝ S).sum_mem (fun i _ => hp i) hp1
      (fun i _ => subset_convexHull ℝ S ⟨ρ i, hρ i, rfl⟩)
  obtain ⟨ι, hι, z, w, hzS, hai, hw, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hx
  have hcard : Fintype.card ι ≤ KK I := by
    have h1 := hai.card_le_finrank_succ
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤
        Module.finrank ℝ (Matrix I I ℂ × ℝ) := Submodule.finrank_le _
    simp only [KK]; omega
  let e : ι ↪ Fin (KK I) := (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hcard)
  have hz : ∀ i, ∃ r ∈ Dens I, z i = (r, h r) := fun i => hzS ⟨i, rfl⟩
  choose r hr hrz using hz
  obtain ⟨ρ0⟩ : Nonempty (Dens I) := by
    obtain ⟨i0⟩ := ‹Nonempty I›
    refine ⟨⟨Matrix.diagonal (fun i => if i = i0 then (1 : ℂ) else 0), ?_, ?_⟩⟩
    · rw [Matrix.posSemidef_diagonal_iff]; intro i; split_ifs <;> norm_num
    · simp [Matrix.trace_diagonal]
  let q : Fin (KK I) → ℝ := Function.extend e w 0
  let σ : Fin (KK I) → Matrix I I ℂ := Function.extend e r (fun _ => ρ0.1)
  have hq : ∀ i, q (e i) = w i := fun i => e.injective.extend_apply _ _ _
  have hσ : ∀ i, σ (e i) = r i := fun i => e.injective.extend_apply _ _ _
  have hq0 : ∀ j ∉ Set.range e, q j = 0 := fun j hj => by
    simp only [q]; rw [Function.extend_apply' _ _ _ (by simpa using hj)]; rfl
  have hs1 : ∑ j, q j = ∑ i, q (e i) :=
    (Fintype.sum_of_injective e e.injective _ _ (fun j hj => hq0 j hj) (fun i => rfl)).symm
  have hs2 : ∑ j, q j • σ j = ∑ i, q (e i) • σ (e i) :=
    (Fintype.sum_of_injective e e.injective _ (fun j => q j • σ j)
      (fun j hj => by simp [hq0 j hj]) (fun i => rfl)).symm
  have hs3 : ∑ j, q j * h (σ j) = ∑ i, q (e i) * h (σ (e i)) :=
    (Fintype.sum_of_injective e e.injective _ (fun j => q j * h (σ j))
      (fun j hj => by simp [hq0 j hj]) (fun i => rfl)).symm
  have hfst := congrArg Prod.fst hwz
  have hsnd := congrArg Prod.snd hwz
  simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hfst hsnd
  refine ⟨q, σ, fun j => ?_, ?_, fun j => ?_, ?_, ?_⟩
  · by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj; rw [hq]; exact (hw i).le
    · rw [hq0 j hj]
  · rw [hs1]; simp only [hq]; exact hw1
  · by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj; rw [hσ]; exact hr i
    · simp only [σ]; rw [Function.extend_apply' _ _ _ (by simpa using hj)]; exact ρ0.2
  · rw [hs2]
    simp only [hq, hσ]
    rw [← hfst]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrz i]
  · rw [hs3]
    simp only [hq, hσ]
    rw [← hsnd]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hrz i]

/-- maxima of `g(Σ p ρ) - Σ p h(ρ)` over finite ensembles of densities are attained, with a
fixed number `KK I` of members. -/
theorem att [Nonempty I] (g h : Matrix I I ℂ → ℝ) (hg : ContinuousOn g (Dens I))
    (hh : ContinuousOn h (Dens I)) :
    ∃ (q : Fin (KK I) → ℝ) (σ : Fin (KK I) → Matrix I I ℂ), (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧
      (∀ i, σ i ∈ Dens I) ∧
      ∀ (k : ℕ) (p : Fin k → ℝ) (ρ : Fin k → Matrix I I ℂ), (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
        (∀ i, ρ i ∈ Dens I) →
        g (∑ i, p i • ρ i) - ∑ i, p i * h (ρ i) ≤ g (∑ i, q i • σ i) - ∑ i, q i * h (σ i) := by
  let Ω : Set ((Fin (KK I) → ℝ) × (Fin (KK I) → Matrix I I ℂ)) :=
    stdSimplex ℝ (Fin (KK I)) ×ˢ Set.pi Set.univ (fun _ => Dens I)
  have hΩ : IsCompact Ω := (isCompact_stdSimplex ℝ _).prod (isCompact_univ_pi fun _ => dens_compact)
  let F : ((Fin (KK I) → ℝ) × (Fin (KK I) → Matrix I I ℂ)) → ℝ :=
    fun x => g (∑ i, x.1 i • x.2 i) - ∑ i, x.1 i * h (x.2 i)
  have hmemΩ : ∀ x ∈ Ω, (∀ i, 0 ≤ x.1 i) ∧ ∑ i, x.1 i = 1 ∧ ∀ i, x.2 i ∈ Dens I := by
    rintro x ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun i => h3 i (Set.mem_univ i)⟩
  have hF : ContinuousOn F Ω := by
    refine ContinuousOn.sub ?_ ?_
    · refine hg.comp (by fun_prop) fun x hx => ?_
      obtain ⟨h1, h2, h3⟩ := hmemΩ x hx
      exact dens_avg _ _ h1 h2 h3
    · refine continuousOn_finset_sum _ fun i _ => ?_
      refine (continuous_apply i |>.comp continuous_fst).continuousOn.mul ?_
      refine hh.comp (continuous_apply i |>.comp continuous_snd).continuousOn fun x hx => ?_
      exact (hmemΩ x hx).2.2 i
  obtain ⟨ρ0, hρ0⟩ : ∃ ρ0 : Matrix I I ℂ, ρ0 ∈ Dens I := by
    obtain ⟨i0⟩ := ‹Nonempty I›
    refine ⟨Matrix.diagonal (fun i => if i = i0 then (1 : ℂ) else 0), ?_, ?_⟩
    · rw [Matrix.posSemidef_diagonal_iff]; intro i; split_ifs <;> norm_num
    · simp [Matrix.trace_diagonal]
  have hne : Ω.Nonempty := by
    refine ⟨(Pi.single 0 1, fun _ => ρ0), ⟨⟨fun i => ?_, ?_⟩, fun i _ => hρ0⟩⟩
    · by_cases hi : i = 0
      · subst hi; simp
      · simp [hi]
    · simp
  obtain ⟨x, hx, hmax⟩ := hΩ.exists_isMaxOn hne hF
  obtain ⟨h1, h2, h3⟩ := hmemΩ x hx
  refine ⟨x.1, x.2, h1, h2, h3, fun k p ρ hp hp1 hρ => ?_⟩
  obtain ⟨q, σ, hq, hq1, hσ, havg, hsum⟩ := red h p ρ hp hp1 hρ
  have hy : (q, σ) ∈ Ω := ⟨⟨hq, hq1⟩, fun i _ => hσ i⟩
  have := hmax hy
  simp only [Set.mem_setOf_eq, F] at this
  rw [havg, hsum] at this
  exact this

end X6AT


/-! Continuity of the von Neumann entropy on density matrices; partial traces of densities. -/

open scoped ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6AT
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Re tr (M log M)`. -/
def Hn' (M : Matrix n n ℂ) : ℝ := (trace (cfc (fun x : ℝ => x * Real.log x) M)).re

lemma vn_eq' (M : Matrix n n ℂ) : QAlgorithms.vnEntropy M = - Hn' M / Real.log 2 := by
  unfold QAlgorithms.vnEntropy Hn'
  have : (fun x : ℝ => x * Real.logb 2 x) = fun x => (Real.log 2)⁻¹ * (x * Real.log x) := by
    funext x; rw [Real.logb]; ring
  rw [this, cfc_const_mul (Real.log 2)⁻¹ (fun x : ℝ => x * Real.log x) M
    Real.continuous_mul_log.continuousOn, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  ring

lemma spec_density' {M : Matrix n n ℂ} (hM : M.PosSemidef) (htr : M.trace = 1) :
    spectrum ℝ M ⊆ Set.Icc 0 1 := by
  intro x hx
  rw [hM.1.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  have h0 := hM.eigenvalues_nonneg
  refine ⟨h0 i, ?_⟩
  have hs := hM.1.trace_eq_sum_eigenvalues
  rw [htr] at hs
  have hs' : ∑ j, hM.1.eigenvalues j = 1 := by
    have := congrArg Complex.re hs
    simpa using this.symm
  rw [← hs']
  exact Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)

lemma cont_tr_re' : Continuous fun M : Matrix n n ℂ => (trace M).re :=
  Complex.continuous_re.comp
    (LinearMap.continuous_of_finiteDimensional (traceLinearMap n ℂ ℂ))

lemma vn_contOn : ContinuousOn (QAlgorithms.vnEntropy : Matrix n n ℂ → ℝ) (Dens n) := by
  have h : ContinuousOn (Hn' : Matrix n n ℂ → ℝ)
      {a | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Set.Icc 0 1} :=
    cont_tr_re'.comp_continuousOn
      (continuousOn_cfc (Matrix n n ℂ) isCompact_Icc _ Real.continuous_mul_log.continuousOn)
  have hsub : Dens n ⊆ {a : Matrix n n ℂ | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Set.Icc 0 1} :=
    fun ρ hρ => ⟨hρ.1.1, spec_density' hρ.1 hρ.2⟩
  have h2 : ContinuousOn (fun ρ : Matrix n n ℂ => -Hn' ρ / Real.log 2) (Dens n) :=
    ((h.mono hsub).neg).div_const _
  exact h2.congr fun ρ _ => vn_eq' ρ

section ptr
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma traceRight_psd {M : Matrix (α × β) (α × β) ℂ} (hM : M.PosSemidef) :
    (QAlgorithms.traceRight M).PosSemidef := by
  let P : β → Matrix (α × β) α ℂ := fun h => of fun x a => if x = (a, h) then 1 else 0
  have : QAlgorithms.traceRight M = ∑ h, (P h)ᴴ * M * P h := by
    ext j k
    simp only [QAlgorithms.traceRight, of_apply, Matrix.sum_apply, mul_apply, conjTranspose_apply, P]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_eq_single (k, h)]
    · rw [Finset.sum_eq_single (j, h)] <;> simp (config := {contextual := true})
    · intro b _ hb; simp [hb]
    · simp
  rw [this]
  exact Matrix.posSemidef_sum _ fun h _ => hM.conjTranspose_mul_mul_same _

lemma trace_traceRight (M : Matrix (α × β) (α × β) ℂ) :
    (QAlgorithms.traceRight M).trace = M.trace := by
  simp only [QAlgorithms.traceRight, trace, diag, of_apply]
  rw [Fintype.sum_prod_type]

lemma traceRight_cont : Continuous (QAlgorithms.traceRight : Matrix (α × β) (α × β) ℂ → _) := by
  unfold QAlgorithms.traceRight
  refine continuous_pi fun j => continuous_pi fun k => ?_
  simp only [of_apply]
  exact continuous_finsetSum _ fun h _ =>
    (continuous_apply (k, h)).comp (continuous_apply (j, h))

end ptr

end X6AT


/-! Claimed50.P24: attained HSW maxima for a fixed dilation. -/

open scoped Matrix ComplexConjugate ComplexOrder
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6P24
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P24
open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I B E : Type} [Fintype I] [Fintype B] [Fintype E]
  [DecidableEq I] [DecidableEq B] [DecidableEq E] [Nonempty I] [Nonempty B] [Nonempty E]

lemma recv_dens (V : Dilation I B E) (hV : IsIsometry V) {ρ : Matrix I I ℂ}
    (hρ : ρ ∈ X6AT.Dens I) : receiverChannel V ρ ∈ X6AT.Dens B := by
  constructor
  · exact X6AT.traceRight_psd (hρ.1.mul_mul_conjTranspose_same V)
  · unfold receiverChannel
    rw [X6AT.trace_traceRight, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    unfold IsIsometry at hV
    rw [hV, Matrix.one_mul, hρ.2]

lemma recv_cont (V : Dilation I B E) : Continuous (receiverChannel V) := by
  unfold receiverChannel
  exact X6AT.traceRight_cont.comp ((continuous_const.matrix_mul continuous_id).matrix_mul
    continuous_const)

lemma g_cont (V : Dilation I B E) (hV : IsIsometry V) :
    ContinuousOn (fun ρ => vnEntropy (receiverChannel V ρ)) (X6AT.Dens I) :=
  X6AT.vn_contOn.comp (recv_cont V).continuousOn fun _ hρ => recv_dens V hV hρ

/-- flatten the two labels into one. -/
lemma flat {M : Type*} [AddCommMonoid M] {nx ny : ℕ} (F : Fin nx → Fin ny → M) :
    ∑ x, ∑ y, F x y = ∑ k : Fin (nx * ny), F (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := by
  rw [Equiv.sum_comp finProdFinEquiv.symm (fun xy => F xy.1 xy.2), Fintype.sum_prod_type]

lemma avg_eq (A : TwoLabelEnsemble I) :
    A.average = ∑ x, ∑ y, A.prob x y • A.state x y := by
  unfold TwoLabelEnsemble.average
  simp only [Complex.coe_smul]

lemma single_eq (V : Dilation I B E) (A : TwoLabelEnsemble I) (hA : A.Valid) (h1 : A.ny = 1) :
    infoXB V A = infoXYB V A := by
  have y0 : Fin A.ny := ⟨0, by omega⟩
  have hy : ∀ y : Fin A.ny, y = y0 := fun y => Fin.ext (by have := y.2; omega)
  have hs : ∀ (f : Fin A.ny → ℝ), ∑ y, f y = f y0 := fun f =>
    Fintype.sum_eq_single y0 fun y hy' => absurd (hy y) hy'
  unfold infoXB infoXYB entropyBX
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hs]
  have hpx : A.px x = A.prob x y0 := by unfold TwoLabelEnsemble.px; exact hs _
  by_cases h0 : A.px x = 0
  · rw [h0, ← hpx, h0]; simp
  · have : A.inputX x = A.state x y0 := by
      unfold TwoLabelEnsemble.inputX
      rw [if_neg h0]
      rw [Fintype.sum_eq_single y0 fun y hy' => absurd (hy y) hy', ← hpx, div_self h0]
      simp
    rw [this, hpx]

theorem hsw (V : Dilation I B E) (hV : PhysicalDilation V) :
    EqualMax (values (infoXYB V)) (singleValues (infoXB V)) := by
  have hiso : IsIsometry V := hV.2.2.2
  obtain ⟨q, σ, hq, hq1, hσ, hmax⟩ := X6AT.att _ _ (g_cont V hiso) (g_cont V hiso)
  let A0 : TwoLabelEnsemble I := ⟨X6AT.KK I, 1, fun x _ => q x, fun x _ => σ x⟩
  have hA0 : A0.Valid := by
    refine ⟨by simp [A0], by simp [A0], fun x _ => hq x, ?_, fun x _ => hσ x⟩
    simp [A0, hq1]
  have hval : ∀ A : TwoLabelEnsemble I, A.Valid → infoXYB V A ≤ infoXYB V A0 := by
    intro A hA
    obtain ⟨-, -, hp, hp1, hst⟩ := hA
    have h := hmax (A.nx * A.ny) (fun k => A.prob (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
      (fun k => A.state (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
      (fun k => hp _ _) (by rw [← flat (fun x y => A.prob x y)]; exact hp1) (fun k => hst _ _)
    have e1 : infoXYB V A = vnEntropy (receiverChannel V (∑ k : Fin (A.nx * A.ny),
        A.prob (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 •
          A.state (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) -
        ∑ k : Fin (A.nx * A.ny), A.prob (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 *
          vnEntropy (receiverChannel V
            (A.state (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)) := by
      unfold infoXYB entropyB
      rw [avg_eq, flat (fun x y => A.prob x y • A.state x y),
        flat (fun x y => A.prob x y * vnEntropy (receiverChannel V (A.state x y)))]
    have e2 : infoXYB V A0 = vnEntropy (receiverChannel V (∑ i, q i • σ i)) -
        ∑ i, q i * vnEntropy (receiverChannel V (σ i)) := by
      unfold infoXYB entropyB
      rw [avg_eq]
      simp [A0]
    rw [e1, e2]; exact h
  refine ⟨infoXYB V A0, ⟨⟨A0, hA0, rfl⟩, ?_⟩, ⟨⟨A0, hA0, rfl, (single_eq V A0 hA0 rfl).symm⟩, ?_⟩⟩
  · rintro z ⟨A, hA, rfl⟩; exact hval A hA
  · rintro z ⟨A, hA, h1, rfl⟩; rw [single_eq V A hA h1]; exact hval A hA

end X6P24


section
open QAlgorithms.Papers.Independent.Claimed50.P24
open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel erasureDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I B E J D F : Type}
variable [Fintype I] [Fintype B] [Fintype E] [Fintype J] [Fintype D] [Fintype F]
variable [DecidableEq I] [DecidableEq B] [DecidableEq E]
variable [DecidableEq J] [DecidableEq D] [DecidableEq F]
variable [Nonempty I] [Nonempty B] [Nonempty E]
variable [Nonempty J] [Nonempty D] [Nonempty F]

theorem solution (V : Dilation I B E) (hV : PhysicalDilation V) :
    EqualMax (values (infoXYB V)) (singleValues (infoXB V)) :=
  X6P24.hsw V hV

end
