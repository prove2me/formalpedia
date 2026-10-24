-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P24.degradableTradeoffs
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T07:44:30.593269+00:00
-- url     : https://prove2.me/submissions/0faf12e4-eb11-4374-a9fb-2a17fc077c7a

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P24
import Theorems.Thm_TroppMatrixConcentration_ch8_entropy_joint_convex
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P33


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


/-! Claimed50.P24: attained private-information maxima. -/

open scoped Matrix ComplexConjugate ComplexOrder
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6P24
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P24
open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

section tl
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

lemma traceLeft_eq (M : Matrix (α × β) (α × β) ℂ) :
    QAlgorithms.traceLeft M = QAlgorithms.traceRight (reindex (Equiv.prodComm _ _)
      (Equiv.prodComm _ _) M) := by
  ext j k
  simp [QAlgorithms.traceLeft, QAlgorithms.traceRight]

end tl

variable {I B E : Type} [Fintype I] [Fintype B] [Fintype E]
  [DecidableEq I] [DecidableEq B] [DecidableEq E] [Nonempty I] [Nonempty B] [Nonempty E]

lemma comp_dens (V : Dilation I B E) (hV : IsIsometry V) {ρ : Matrix I I ℂ}
    (hρ : ρ ∈ X6AT.Dens I) : complementaryChannel V ρ ∈ X6AT.Dens E := by
  unfold complementaryChannel
  rw [traceLeft_eq]
  have hP : (V * ρ * Vᴴ).PosSemidef := hρ.1.mul_mul_conjTranspose_same V
  constructor
  · exact X6AT.traceRight_psd (hP.submatrix _)
  · rw [X6AT.trace_traceRight]
    have : (reindex (Equiv.prodComm B E) (Equiv.prodComm B E) (V * ρ * Vᴴ)).trace =
        (V * ρ * Vᴴ).trace := by
      simp only [Matrix.trace, Matrix.diag, reindex_apply, submatrix_apply]
      exact Equiv.sum_comp (Equiv.prodComm B E).symm (fun i => (V * ρ * Vᴴ) i i)
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    unfold IsIsometry at hV
    rw [hV, Matrix.one_mul, hρ.2]

lemma comp_cont (V : Dilation I B E) : Continuous (complementaryChannel V) := by
  have : complementaryChannel V = fun ρ => QAlgorithms.traceRight (reindex (Equiv.prodComm B E)
      (Equiv.prodComm B E) (V * ρ * Vᴴ)) := by
    funext ρ; unfold complementaryChannel; rw [traceLeft_eq]
  rw [this]
  refine X6AT.traceRight_cont.comp ?_
  refine Continuous.matrix_submatrix ?_ _ _
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

/-- the private-information integrand. -/
def G (V : Dilation I B E) (ρ : Matrix I I ℂ) : ℝ :=
  vnEntropy (receiverChannel V ρ) - vnEntropy (complementaryChannel V ρ)

lemma G_cont (V : Dilation I B E) (hV : IsIsometry V) : ContinuousOn (G V) (X6AT.Dens I) :=
  (g_cont V hV).sub
    (X6AT.vn_contOn.comp (comp_cont V).continuousOn fun _ hρ => comp_dens V hV hρ)

lemma single_sum (A : TwoLabelEnsemble I) (h1 : A.ny = 1) (f : Matrix I I ℂ → ℝ) :
    ∑ x, A.px x * f (A.inputX x) = ∑ x, ∑ y, A.prob x y * f (A.state x y) := by
  have y0 : Fin A.ny := ⟨0, by omega⟩
  have hy : ∀ y : Fin A.ny, y = y0 := fun y => Fin.ext (by have := y.2; omega)
  have hs : ∀ (f : Fin A.ny → ℝ), ∑ y, f y = f y0 := fun f =>
    Fintype.sum_eq_single y0 fun y hy' => absurd (hy y) hy'
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

theorem private_dir (V : Dilation I B E) (hV : PhysicalDilation V) :
    EqualMax (values (fun A => infoYBX V A - infoYEX V A))
      (singleValues (fun A => infoXB V A - infoXE V A)) := by
  have hiso : IsIsometry V := hV.2.2.2
  obtain ⟨q, σ, hq, hq1, hσ, hmax⟩ := X6AT.att _ _ (G_cont V hiso) (G_cont V hiso)
  set M := G V (∑ i, q i • σ i) - ∑ i, q i * G V (σ i) with hM
  have hL : ∀ A : TwoLabelEnsemble I, infoYBX V A - infoYEX V A =
      ∑ x, A.px x * G V (A.inputX x) - ∑ x, ∑ y, A.prob x y * G V (A.state x y) := by
    intro A
    unfold infoYBX infoYEX entropyBX entropyEX G
    simp only [mul_sub, Finset.sum_sub_distrib]; ring
  have hR : ∀ A : TwoLabelEnsemble I, infoXB V A - infoXE V A =
      G V A.average - ∑ x, A.px x * G V (A.inputX x) := by
    intro A
    unfold infoXB infoXE entropyB entropyBX entropyEX G
    simp only [mul_sub, Finset.sum_sub_distrib]; ring
  -- left bound
  have hLb : ∀ A : TwoLabelEnsemble I, A.Valid → infoYBX V A - infoYEX V A ≤ M := by
    intro A hA
    obtain ⟨-, -, hp, hp1, hst⟩ := hA
    rw [hL, ← Finset.sum_sub_distrib]
    have hpx1 : ∑ x, A.px x = 1 := hp1
    calc _ ≤ ∑ x, A.px x * M := Finset.sum_le_sum fun x _ => ?_
      _ = M := by rw [← Finset.sum_mul, hpx1, one_mul]
    by_cases h0 : A.px x = 0
    · have hz : ∀ y, A.prob x y = 0 := fun y =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hp x y)).1 h0 y (Finset.mem_univ y)
      simp [h0, hz]
    · have hpos : 0 < A.px x := lt_of_le_of_ne (Finset.sum_nonneg fun y _ => hp x y) (Ne.symm h0)
      have h := hmax A.ny (fun y => A.prob x y / A.px x) (A.state x)
        (fun y => div_nonneg (hp x y) hpos.le)
        (by rw [← Finset.sum_div]; exact div_self h0) (hst x)
      have hin : A.inputX x = ∑ y, (A.prob x y / A.px x) • A.state x y := by
        unfold TwoLabelEnsemble.inputX; rw [if_neg h0]; simp only [Complex.coe_smul]
      rw [← hin] at h
      have h2 := mul_le_mul_of_nonneg_left h hpos.le
      have h3 : A.px x * ∑ y, A.prob x y / A.px x * G V (A.state x y) =
          ∑ y, A.prob x y * G V (A.state x y) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun y _ => ?_; field_simp
      rw [mul_sub, h3] at h2
      exact h2
  -- right bound
  have hRb : ∀ A : TwoLabelEnsemble I, A.Valid → A.ny = 1 → infoXB V A - infoXE V A ≤ M := by
    intro A hA h1
    obtain ⟨-, -, hp, hp1, hst⟩ := hA
    rw [hR, single_sum A h1, avg_eq, flat (fun x y => A.prob x y • A.state x y),
      flat (fun x y => A.prob x y * G V (A.state x y))]
    exact hmax _ _ _ (fun k => hp _ _) (by rw [← flat (fun x y => A.prob x y)]; exact hp1)
      (fun k => hst _ _)
  let A0 : TwoLabelEnsemble I := ⟨X6AT.KK I, 1, fun x _ => q x, fun x _ => σ x⟩
  have hA0 : A0.Valid := by
    refine ⟨by simp [A0], by simp [A0], fun x _ => hq x, ?_, fun x _ => hσ x⟩
    simp [A0, hq1]
  let A1 : TwoLabelEnsemble I := ⟨1, X6AT.KK I, fun _ y => q y, fun _ y => σ y⟩
  have hA1 : A1.Valid := by
    refine ⟨by simp [A1], by simp [A1], fun _ y => hq y, ?_, fun _ y => hσ y⟩
    simp [A1, hq1]
  have v0 : infoXB V A0 - infoXE V A0 = M := by
    rw [hR, single_sum A0 rfl, avg_eq]
    simp [A0, hM]
  have v1 : infoYBX V A1 - infoYEX V A1 = M := by
    rw [hL]
    have hpx : ∀ x, A1.px x = 1 := fun x => by simp [TwoLabelEnsemble.px, A1, hq1]
    have hin : ∀ x, A1.inputX x = ∑ i, q i • σ i := by
      intro x
      unfold TwoLabelEnsemble.inputX
      rw [if_neg (by rw [hpx]; norm_num), hpx]
      simp [A1, Complex.coe_smul]
    simp only [hpx, hin, one_mul]
    simp [A1, hM]
  refine ⟨M, ⟨⟨A1, hA1, v1.symm⟩, ?_⟩, ⟨⟨A0, hA0, rfl, v0.symm⟩, ?_⟩⟩
  · rintro z ⟨A, hA, rfl⟩; exact hLb A hA
  · rintro z ⟨A, hA, h1, rfl⟩; exact hRb A hA h1

end X6P24


/-! X6 SSA library, part 1: star-algebra homomorphisms between matrix algebras commute with the
functional calculus; joint convexity of Tropp's relative entropy on arbitrary finite index types;
unitary invariance. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix
noncomputable section
namespace X6SSA
open TroppMatrixConcentration Matrix

variable {m n ι : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Fintype ι] [DecidableEq ι]

lemma cont_hom (φ : Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ) : Continuous φ :=
  LinearMap.continuous_of_finiteDimensional (φ.toAlgHom.toLinearMap)

lemma map_cfc_mat (φ : Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ) (f : ℝ → ℝ) (A : Matrix m m ℂ)
    (hA : A.IsHermitian) : φ (cfc f A) = cfc f (φ A) := by
  have hA' : IsSelfAdjoint A := hA
  have hφ : IsSelfAdjoint (φ A) := by
    rw [IsSelfAdjoint, ← map_star, hA'.star_eq]
  exact StarAlgHomClass.map_cfc φ f A (A.finite_real_spectrum.continuousOn f) (cont_hom φ) hA' hφ

/-- `M ↦ M ⊗ I`. -/
def kronR (n : Type*) [Fintype n] [DecidableEq n] : Matrix m m ℂ →⋆ₐ[ℂ] Matrix (m × n) (m × n) ℂ where
  toFun M := M ⊗ₖ (1 : Matrix n n ℂ)
  map_one' := one_kronecker_one
  map_mul' M N := by rw [← mul_kronecker_mul, mul_one]
  map_zero' := zero_kronecker _
  map_add' M N := add_kronecker _ _ _
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [smul_kronecker, one_kronecker_one]
  map_star' M := by
    simp only [star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one]

/-- `M ↦ I ⊗ M`. -/
def kronL (n : Type*) [Fintype n] [DecidableEq n] : Matrix m m ℂ →⋆ₐ[ℂ] Matrix (n × m) (n × m) ℂ where
  toFun M := (1 : Matrix n n ℂ) ⊗ₖ M
  map_one' := one_kronecker_one
  map_mul' M N := by rw [← mul_kronecker_mul, mul_one]
  map_zero' := kronecker_zero _
  map_add' M N := kronecker_add _ _ _
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [kronecker_smul, one_kronecker_one]
  map_star' M := by
    simp only [star_eq_conjTranspose, conjTranspose_kronecker, conjTranspose_one]

@[simp] lemma kronR_apply (M : Matrix m m ℂ) : kronR n M = M ⊗ₖ (1 : Matrix n n ℂ) := rfl
@[simp] lemma kronL_apply (M : Matrix m m ℂ) : kronL n M = (1 : Matrix n n ℂ) ⊗ₖ M := rfl

/-- reindexing as a star-algebra equivalence. -/
def reind (e : m ≃ n) : Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ where
  toFun M := reindex e e M
  map_one' := by simp
  map_mul' M N := by simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  map_zero' := by simp
  map_add' M N := by ext i j; simp
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    ext i j; simp [Matrix.one_apply]
  map_star' M := by
    simp [star_eq_conjTranspose, Matrix.reindex_apply, conjTranspose_submatrix]

@[simp] lemma reind_apply (e : m ≃ n) (M : Matrix m m ℂ) : reind e M = reindex e e M := rfl

lemma trace_reind (e : m ≃ n) (M : Matrix m m ℂ) : (reindex e e M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.reindex_apply, Matrix.diag_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => M i i)

lemma relEnt_reind (e : m ≃ n) (A H : Matrix m m ℂ) (hA : A.IsHermitian) (hH : H.IsHermitian) :
    ch8_relativeEntropy (reindex e e A) (reindex e e H) = ch8_relativeEntropy A H := by
  unfold ch8_relativeEntropy matrixLog
  have h1 := map_cfc_mat (reind e) Real.log A hA
  have h2 := map_cfc_mat (reind e) Real.log H hH
  simp only [reind_apply] at h1 h2
  rw [← h1, ← h2, ← trace_reind e]
  congr 2
  simp only [← reind_apply, ← map_mul, ← map_sub]

lemma posDef_reind (e : m ≃ n) {A : Matrix m m ℂ} (hA : A.PosDef) : (reindex e e A).PosDef := by
  rw [Matrix.reindex_apply]; exact hA.submatrix e.symm.injective

/-- Joint convexity of relative entropy on an arbitrary nonempty finite index type. -/
theorem joint_convex [Nonempty ι] :
    ConvexOn ℝ {P : Matrix ι ι ℂ × Matrix ι ι ℂ | P.1.PosDef ∧ P.2.PosDef}
      (fun P => ch8_relativeEntropy P.1 P.2) := by
  set e := Fintype.equivFin ι
  haveI : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  have hc := (ch8_entropy_joint_convex (d := Fintype.card ι))
  let L : (Matrix ι ι ℂ × Matrix ι ι ℂ) →ₗ[ℝ]
      (Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ ×
        Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) :=
    LinearMap.prodMap ((reindexLinearEquiv ℂ ℂ e e).toLinearMap.restrictScalars ℝ)
      ((reindexLinearEquiv ℂ ℂ e e).toLinearMap.restrictScalars ℝ)
  have h := hc.comp_linearMap L
  have hset : L ⁻¹' {P | P.1.PosDef ∧ P.2.PosDef} =
      {P : Matrix ι ι ℂ × Matrix ι ι ℂ | P.1.PosDef ∧ P.2.PosDef} := by
    ext P
    simp only [Set.mem_preimage, Set.mem_setOf_eq, L, LinearMap.prodMap_apply,
      LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, reindexLinearEquiv_apply]
    constructor
    · rintro ⟨h1, h2⟩
      have k1 := posDef_reind e.symm h1
      have k2 := posDef_reind e.symm h2
      simp only [reindex_apply, submatrix_submatrix, Equiv.symm_symm] at k1 k2
      simpa using And.intro k1 k2
    · rintro ⟨h1, h2⟩; exact ⟨posDef_reind e h1, posDef_reind e h2⟩
  rw [hset] at h
  refine h.congr fun P hP => ?_
  simp only [Function.comp_apply, L, LinearMap.prodMap_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, reindexLinearEquiv_apply]
  exact relEnt_reind e _ _ hP.1.isHermitian hP.2.isHermitian

/-- Finite Jensen form of joint convexity. -/
theorem jensen [Nonempty ι] {G : Type*} (s : Finset G) (w : G → ℝ) (hw : ∀ g ∈ s, 0 ≤ w g)
    (hw1 : ∑ g ∈ s, w g = 1) (A H : G → Matrix ι ι ℂ) (hA : ∀ g ∈ s, (A g).PosDef)
    (hH : ∀ g ∈ s, (H g).PosDef) :
    ch8_relativeEntropy (∑ g ∈ s, w g • A g) (∑ g ∈ s, w g • H g) ≤
      ∑ g ∈ s, w g * ch8_relativeEntropy (A g) (H g) := by
  have := (joint_convex (ι := ι)).map_sum_le hw hw1 (p := fun g => (A g, H g))
    (fun g hg => ⟨hA g hg, hH g hg⟩)
  have e1 : (∑ i ∈ s, w i • (A i, H i)).1 = ∑ g ∈ s, w g • A g := by simp [Prod.fst_sum]
  have e2 : (∑ i ∈ s, w i • (A i, H i)).2 = ∑ g ∈ s, w g • H g := by simp [Prod.snd_sum]
  rw [e1, e2] at this
  simpa only [smul_eq_mul] using this

/-- Unitary invariance of relative entropy. -/
lemma relEnt_unitary (U : unitary (Matrix ι ι ℂ)) (A H : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (hH : H.IsHermitian) :
    ch8_relativeEntropy ((U : Matrix ι ι ℂ) * A * star (U : Matrix ι ι ℂ))
      ((U : Matrix ι ι ℂ) * H * star (U : Matrix ι ι ℂ)) = ch8_relativeEntropy A H := by
  set φ : Matrix ι ι ℂ →⋆ₐ[ℂ] Matrix ι ι ℂ :=
    (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix ι ι ℂ).toStarAlgHom
  have hφ : ∀ X, φ X = (U : Matrix ι ι ℂ) * X * star (U : Matrix ι ι ℂ) := fun X => rfl
  unfold ch8_relativeEntropy matrixLog
  rw [← hφ, ← hφ, ← map_cfc_mat φ _ _ hA, ← map_cfc_mat φ _ _ hH, ← map_sub φ (cfc _ A),
    ← map_mul, ← map_sub φ A H, ← map_sub, hφ]
  rw [Matrix.trace_mul_cycle]
  rw [show star (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) = 1 from Unitary.star_mul_self_of_mem U.2,
    one_mul]

end X6SSA


/-! X6 SSA library, part 2: twirling the middle factor of `A × (B × C)` and monotonicity of
relative entropy under the partial trace over `B`. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix
noncomputable section
namespace X6SSA
open TroppMatrixConcentration Matrix

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

def sg (b : Bool) : ℂ := if b then 1 else -1

lemma sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

lemma star_sg (b : Bool) : star (sg b) = sg b := by cases b <;> simp [sg]

omit [Fintype B] in
lemma sg_sum [Fintype B] (u v : B) :
    ∑ s : B → Bool, sg (s u) * sg (s v) = if u = v then (2 : ℂ) ^ Fintype.card B else 0 := by
  split_ifs with h
  · subst h
    simp [sg_mul_self, Fintype.card_fun, Fintype.card_bool]
  · refine Finset.sum_involution (fun s _ => Function.update s v (!s v)) ?_ ?_ ?_ ?_
    · intro s _
      simp only [Function.update_of_ne h, Function.update_self]
      cases s v <;> cases s u <;> simp [sg]
    · intro s _ _ heq
      have := congrFun heq v
      simp only [Function.update_self] at this
      cases hs : s v <;> simp [hs] at this
    · intro s _; exact Finset.mem_univ _
    · intro s _
      ext w
      by_cases hw : w = v
      · subst hw; simp
      · simp [Function.update_of_ne hw]

/-- diagonal sign unitary acting on the middle factor. -/
def Dm (s : B → Bool) : Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  diagonal fun x => sg (s x.2.1)

lemma Dm_mul_self (s : B → Bool) : (Dm s : Matrix (A × (B × C)) _ ℂ) * Dm s = 1 := by
  simp [Dm, diagonal_mul_diagonal, sg_mul_self]

lemma Dm_star (s : B → Bool) : star (Dm s : Matrix (A × (B × C)) _ ℂ) = Dm s := by
  rw [Dm, star_eq_conjTranspose, diagonal_conjTranspose]
  congr 1; funext x; exact star_sg _

lemma Dm_mem (s : B → Bool) : (Dm s : Matrix (A × (B × C)) _ ℂ) ∈ unitary _ := by
  rw [Unitary.mem_iff, Dm_star, Dm_mul_self]; exact ⟨rfl, rfl⟩

/-- cyclic shift of the middle factor. -/
def tau {N : ℕ} [NeZero N] (e : B ≃ Fin N) (k : Fin N) : A × (B × C) ≃ A × (B × C) :=
  Equiv.prodCongr (Equiv.refl A)
    (Equiv.prodCongr ((e.trans (Equiv.addRight k)).trans e.symm) (Equiv.refl C))

lemma tau_symm_apply {N : ℕ} [NeZero N] (e : B ≃ Fin N) (k : Fin N) (x : A × (B × C)) :
    (tau e k).symm x = (x.1, (e.symm (e x.2.1 - k), x.2.2)) := by
  simp [tau, Equiv.prodCongr, sub_eq_add_neg]; rfl

/-- one element of the twirling group. -/
def term {N : ℕ} [NeZero N] (e : B ≃ Fin N) (g : Fin N × (B → Bool))
    (M : Matrix (A × (B × C)) (A × (B × C)) ℂ) : Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  Dm g.2 * reindex (tau e g.1) (tau e g.1) M * Dm g.2

lemma term_apply {N : ℕ} [NeZero N] (e : B ≃ Fin N) (g : Fin N × (B → Bool))
    (M : Matrix (A × (B × C)) (A × (B × C)) ℂ) (x y : A × (B × C)) :
    term e g M x y = sg (g.2 x.2.1) * sg (g.2 y.2.1) *
      M (x.1, (e.symm (e x.2.1 - g.1), x.2.2)) (y.1, (e.symm (e y.2.1 - g.1), y.2.2)) := by
  simp only [term, Dm, diagonal_mul, mul_diagonal, reindex_apply, submatrix_apply,
    tau_symm_apply]
  ring

/-- partial trace over the middle factor. -/
def trB (M : Matrix (A × (B × C)) (A × (B × C)) ℂ) : Matrix (A × C) (A × C) ℂ :=
  of fun p q => ∑ b, M (p.1, (b, p.2)) (q.1, (b, q.2))

/-- the equivalence `(A × C) × B ≃ A × (B × C)`. -/
def eqv : (A × C) × B ≃ A × (B × C) where
  toFun z := (z.1.1, (z.2, z.1.2))
  invFun x := ((x.1, x.2.2), x.2.1)
  left_inv z := rfl
  right_inv x := rfl

/-- `N ↦ N ⊗ I_B` placed in the middle. -/
def midH : Matrix (A × C) (A × C) ℂ →⋆ₐ[ℂ] Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  (reind (eqv (A := A) (B := B) (C := C))).comp (kronR B)

lemma midH_apply (N : Matrix (A × C) (A × C) ℂ) (x y : A × (B × C)) :
    midH N x y = if x.2.1 = y.2.1 then N (x.1, x.2.2) (y.1, y.2.2) else 0 := by
  show N (x.1, x.2.2) (y.1, y.2.2) * (1 : Matrix B B ℂ) x.2.1 y.2.1 = _
  rw [one_apply]
  split_ifs <;> simp

lemma twirl {N : ℕ} [NeZero N] (e : B ≃ Fin N) (M : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    ∑ g : Fin N × (B → Bool), term e g M = ((2 : ℂ) ^ Fintype.card B) • midH (trB M) := by
  ext x y
  rw [Matrix.sum_apply, Fintype.sum_prod_type, Matrix.smul_apply, midH_apply]
  simp only [term_apply]
  have : ∀ k : Fin N, ∑ s : B → Bool, sg (s x.2.1) * sg (s y.2.1) *
      M (x.1, (e.symm (e x.2.1 - k), x.2.2)) (y.1, (e.symm (e y.2.1 - k), y.2.2)) =
      (if x.2.1 = y.2.1 then (2 : ℂ) ^ Fintype.card B else 0) *
      M (x.1, (e.symm (e x.2.1 - k), x.2.2)) (y.1, (e.symm (e y.2.1 - k), y.2.2)) := by
    intro k; rw [← sg_sum, Finset.sum_mul]
  simp only [this]
  split_ifs with h
  · rw [← Finset.mul_sum, smul_eq_mul]
    congr 1
    simp only [trB, of_apply, h]
    rw [← Equiv.sum_comp e.symm]
    exact (Equiv.sum_comp (Equiv.subLeft (e y.2.1))
      (fun j => M (x.1, (e.symm j, x.2.2)) (y.1, (e.symm j, y.2.2))))
  · simp

lemma term_posDef {N : ℕ} [NeZero N] (e : B ≃ Fin N) (g : Fin N × (B → Bool))
    {M : Matrix (A × (B × C)) (A × (B × C)) ℂ} (hM : M.PosDef) : (term e g M).PosDef := by
  have h := (posDef_reind (tau e g.1) hM).mul_mul_conjTranspose_same (B := Dm g.2) (by
    intro u v huv
    have := congrArg (fun z => z ᵥ* Dm g.2) huv
    simpa [vecMul_vecMul, Dm_mul_self] using this)
  rwa [← star_eq_conjTranspose, Dm_star] at h

lemma term_relEnt {N : ℕ} [NeZero N] (e : B ≃ Fin N) (g : Fin N × (B → Bool))
    {M H : Matrix (A × (B × C)) (A × (B × C)) ℂ} (hM : M.IsHermitian) (hH : H.IsHermitian) :
    ch8_relativeEntropy (term e g M) (term e g H) = ch8_relativeEntropy M H := by
  have h := relEnt_unitary (⟨Dm g.2, Dm_mem g.2⟩ : unitary (Matrix (A × (B × C)) (A × (B × C)) ℂ)) (reindex (tau e g.1) (tau e g.1) M)
    (reindex (tau e g.1) (tau e g.1) H) (by rw [reindex_apply]; exact hM.submatrix _)
    (by rw [reindex_apply]; exact hH.submatrix _)
  simp only [Dm_star] at h
  rw [term, term, h, relEnt_reind _ _ _ hM hH]

/-- Monotonicity of relative entropy under the partial trace over the middle factor, in the
form `D(trB ρ ⊗ I/|B|, trB σ ⊗ I/|B|) ≤ D(ρ, σ)`. -/
theorem mono_trB [Nonempty A] [Nonempty B] [Nonempty C]
    (ρ σ : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    ch8_relativeEntropy (((Fintype.card B : ℝ)⁻¹) • midH (B := B) (trB ρ))
      (((Fintype.card B : ℝ)⁻¹) • midH (B := B) (trB σ)) ≤ ch8_relativeEntropy ρ σ := by
  set N := Fintype.card B
  haveI : NeZero N := ⟨Fintype.card_ne_zero⟩
  set e := Fintype.equivFin B
  set w : ℝ := ((N : ℝ) * 2 ^ N)⁻¹
  have hT : ∀ M : Matrix (A × (B × C)) (A × (B × C)) ℂ,
      ((N : ℝ)⁻¹) • midH (B := B) (trB M) = ∑ g : Fin N × (B → Bool), w • term e g M := by
    intro M
    rw [← Finset.smul_sum, twirl]
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, w]
    push_cast
    field_simp
    rfl
  rw [hT, hT]
  have hw1 : ∑ _g : Fin N × (B → Bool), w = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul, w]
    push_cast
    field_simp
    exact mul_div_cancel_left₀ (2 ^ N : ℝ) (Nat.cast_ne_zero.mpr (NeZero.ne N))
  have := jensen (Finset.univ : Finset (Fin N × (B → Bool))) (fun _ => w)
    (fun _ _ => by positivity) hw1 (fun g => term e g ρ) (fun g => term e g σ)
    (fun g _ => term_posDef e g hρ) (fun g _ => term_posDef e g hσ)
  refine this.trans (le_of_eq ?_)
  simp only [term_relEnt e _ hρ.isHermitian hσ.isHermitian, ← Finset.sum_mul, hw1, one_mul]

end X6SSA


/-! X6 SSA library, part 3: strong subadditivity for positive-definite states,
`S(AC) + S(BC) - S(C) - S(ABC) ≥ 0` on `A × (B × C)`, in the form
`ent ρ_AC - ent ρ_C ≤ ent ρ - ent ρ_BC` with `ent M = Re tr (M log M)`. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix MatrixOrder
noncomputable section
namespace X6SSA
open TroppMatrixConcentration Matrix

/-- negative entropy `Re tr (M log M)` (nats). -/
def ent {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) : ℝ :=
  (trace (M * cfc Real.log M)).re

section general
variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

lemma log_smul (N : Matrix n n ℂ) (hN : N.PosDef) {c : ℝ} (hc : 0 < c) :
    cfc Real.log (c • N) = algebraMap ℝ (Matrix n n ℂ) (Real.log c) + cfc Real.log N := by
  have hsa : IsSelfAdjoint N := hN.isHermitian
  have hpos := hN.isStrictlyPositive
  rw [← cfc_comp_smul c Real.log N (by
    refine Real.continuousOn_log.mono ?_
    rintro _ ⟨x, hx, rfl⟩
    have := hpos.spectrum_pos hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, smul_eq_mul]
    positivity)]
  rw [← cfc_const (Real.log c) N, ← cfc_add N (fun _ => Real.log c) Real.log
    (by fun_prop) (by
      refine Real.continuousOn_log.mono fun x hx => ?_
      have := hpos.spectrum_pos hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact this.ne')]
  refine cfc_congr fun x hx => ?_
  have := hpos.spectrum_pos hx
  simp only [smul_eq_mul]
  rw [Real.log_mul hc.ne' this.ne']

lemma posDef_smul {N : Matrix n n ℂ} (hN : N.PosDef) {c : ℝ} (hc : 0 < c) : (c • N).PosDef := by
  have : c • N = (c : ℂ) • N := by ext i j; simp [Complex.real_smul]
  rw [this]; exact hN.smul (by exact_mod_cast hc)

lemma trace_smul_re (c : ℝ) (N : Matrix n n ℂ) : (trace (c • N)).re = c * (trace N).re := by
  rw [trace_smul]; simp [Complex.real_smul]

lemma trace_alg_mul_re (c : ℝ) (N : Matrix n n ℂ) :
    (trace (N * algebraMap ℝ (Matrix n n ℂ) c)).re = c * (trace N).re := by
  rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, trace_smul_re]

/-- relative entropy against a scaled image under a star-algebra homomorphism. -/
lemma relEnt_hom (ρ : Matrix n n ℂ) (φ : Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ) (M : Matrix m m ℂ)
    (hM : M.PosDef) (hφM : (φ M).PosDef) {c : ℝ} (hc : 0 < c) :
    ch8_relativeEntropy ρ (c • φ M) = ent ρ - Real.log c * (trace ρ).re -
      (trace (ρ * φ (cfc Real.log M))).re - (trace ρ).re + c * (trace (φ M)).re := by
  unfold ch8_relativeEntropy matrixLog ent
  rw [log_smul _ hφM hc, ← map_cfc_mat φ _ _ hM.isHermitian]
  simp only [mul_sub, mul_add, trace_sub, trace_add, Complex.sub_re, Complex.add_re,
    trace_alg_mul_re, trace_smul_re]
  ring

lemma ent_hom (φ : Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ) (M : Matrix m m ℂ)
    (hM : M.PosDef) (hφM : (φ M).PosDef) {c : ℝ} (hc : 0 < c) :
    ent (c • φ M) = c * (Real.log c * (trace (φ M)).re + (trace (φ (M * cfc Real.log M))).re) := by
  unfold ent
  rw [log_smul _ hφM hc, ← map_cfc_mat φ _ _ hM.isHermitian, smul_mul_assoc, trace_smul_re,
    mul_add, trace_add, Complex.add_re, trace_alg_mul_re, map_mul]

end general

section ptr
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

/-- partial trace over the first factor. -/
def trF (M : Matrix (P × Q) (P × Q) ℂ) : Matrix Q Q ℂ := of fun q q' => ∑ p, M (p, q) (p, q')

/-- the isometric embedding `x ↦ e_p ⊗ x`. -/
def V (p : P) : Matrix (P × Q) Q ℂ := of fun x q => if x.1 = p ∧ x.2 = q then 1 else 0

lemma V_conj (p : P) (M : Matrix (P × Q) (P × Q) ℂ) :
    (V p : Matrix (P × Q) Q ℂ)ᴴ * M * (V p : Matrix (P × Q) Q ℂ) = of fun q q' => M (p, q) (p, q') := by
  ext q q'
  simp only [mul_apply, conjTranspose_apply, V, of_apply]
  simp [Fintype.sum_prod_type, ite_and, apply_ite (starRingEnd ℂ), ite_mul]

lemma trF_eq (M : Matrix (P × Q) (P × Q) ℂ) : trF M = ∑ p, (V p : Matrix (P × Q) Q ℂ)ᴴ * M * (V p : Matrix (P × Q) Q ℂ) := by
  ext q q'
  simp only [trF, of_apply, V_conj, Matrix.sum_apply]

lemma trF_posDef [Nonempty P] {M : Matrix (P × Q) (P × Q) ℂ} (hM : M.PosDef) : (trF M).PosDef := by
  obtain ⟨p0⟩ := ‹Nonempty P›
  rw [trF_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ p0)]
  refine PosDef.add_posSemidef ?_ (posSemidef_sum _ fun p _ => hM.posSemidef.conjTranspose_mul_mul_same _)
  refine hM.conjTranspose_mul_mul_same fun u v huv => ?_
  funext q
  have := congrFun huv (p0, q)
  simpa [mulVec, dotProduct, V, Prod.ext_iff, Fintype.sum_prod_type, ite_and] using this

lemma trace_trF (M : Matrix (P × Q) (P × Q) ℂ) : trace (trF M) = trace M := by
  simp [trace, trF, Fintype.sum_prod_type]; exact Finset.sum_comm

lemma trace_kronL (L : Matrix Q Q ℂ) : trace (kronL P L) = Fintype.card P * trace L := by
  rw [kronL_apply, trace_kronecker, trace_one]

/-- `tr (ρ (1 ⊗ L)) = tr (trF ρ L)`. -/
lemma trace_mul_kronL (M : Matrix (P × Q) (P × Q) ℂ) (L : Matrix Q Q ℂ) :
    trace (M * kronL P L) = trace (trF M * L) := by
  simp only [trace, diag_apply, mul_apply, kronL_apply, kronecker_apply, one_apply, trF, of_apply,
    Fintype.sum_prod_type]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_ite_eq, Finset.sum_mul, ite_mul, zero_mul]
  have h : ∀ (x : P) (x1 : Q), (∑ x2 : P, ∑ x3 : Q,
      if x2 = x then M (x, x1) (x2, x3) * (1 * L x3 x1) else 0) =
      ∑ x3, M (x, x1) (x, x3) * L x3 x1 := by
    intro x x1; rw [Finset.sum_comm]; simp
  simp only [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]

end ptr

section three
variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

/-- `A × (B × C) ≃ B × (A × C)`. -/
def swp : A × (B × C) ≃ B × (A × C) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun y := (y.2.1, (y.1, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

lemma trB_eq (M : Matrix (A × (B × C)) (A × (B × C)) ℂ) : trB M = trF (reindex swp swp M) := rfl

lemma trB_posDef [Nonempty B] {M : Matrix (A × (B × C)) (A × (B × C)) ℂ} (hM : M.PosDef) :
    (trB M).PosDef := by
  rw [trB_eq]; exact trF_posDef (posDef_reind _ hM)

lemma trace_midH (N : Matrix (A × C) (A × C) ℂ) :
    trace (midH (B := B) N) = Fintype.card B * trace N := by
  simp only [midH, StarAlgHom.comp_apply, reind_apply, trace_reind, kronR_apply,
    trace_kronecker, trace_one]
  ring

lemma midH_posDef {N : Matrix (A × C) (A × C) ℂ} (hN : N.PosDef) : (midH (B := B) N).PosDef := by
  simp only [midH, StarAlgHom.comp_apply, reind_apply, kronR_apply]
  exact posDef_reind _ (hN.kronecker PosDef.one)

lemma kronL_posDef {Q : Type*} [Fintype Q] [DecidableEq Q] {N : Matrix Q Q ℂ} (hN : N.PosDef) :
    (kronL A N).PosDef := by
  rw [kronL_apply]; exact PosDef.one.kronecker hN

lemma trB_kronL (M : Matrix (B × C) (B × C) ℂ) : trB (kronL A M) = kronL A (trF M) := by
  ext x y
  simp [trB, trF, kronecker_apply, one_apply, Finset.mul_sum]

lemma trF_trB (M : Matrix (A × (B × C)) (A × (B × C)) ℂ) : trF (trB M) = trF (trF M) := by
  ext c c'
  simp only [trF, trB, of_apply]
  exact Finset.sum_comm

lemma natmul_re (k : ℕ) (z : ℂ) : ((k : ℂ) * z).re = k * z.re := by simp

lemma hom_rsmul {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (φ : Matrix m m ℂ →⋆ₐ[ℂ] Matrix n n ℂ) (c : ℝ) (X : Matrix m m ℂ) : φ (c • X) = c • φ X := by
  rw [← algebraMap_smul ℂ c X, map_smul, algebraMap_smul]

/-- Strong subadditivity for positive-definite states of trace one. -/
theorem ssa_posDef [Nonempty A] [Nonempty B] [Nonempty C]
    (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hρ : ρ.PosDef) (htr : trace ρ = 1) :
    ent (trB ρ) - ent (trF (trF ρ)) ≤ ent ρ - ent (trF ρ) := by
  have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have h := mono_trB ρ (((Fintype.card A : ℝ)⁻¹) • kronL A (trF ρ)) hρ
    (posDef_smul (kronL_posDef (trF_posDef hρ)) (inv_pos.mpr hA))
  have hρBC := trF_posDef hρ
  have hρAC := trB_posDef (B := B) hρ
  have hρC := trF_posDef hρBC
  have tBC : (trace (trF ρ)).re = 1 := by rw [trace_trF, htr]; simp
  have tAC : (trace (trB ρ)).re = 1 := by rw [trB_eq, trace_trF, trace_reind, htr]; simp
  have tC : (trace (trF (trF ρ))).re = 1 := by rw [trace_trF, tBC]
  -- right-hand side
  have hR := relEnt_hom ρ (kronL A) (trF ρ) hρBC (kronL_posDef hρBC) (inv_pos.mpr hA)
  rw [trace_mul_kronL, trace_kronL, htr, natmul_re, tBC, Complex.one_re] at hR
  -- left-hand side
  have e2 : trB ((Fintype.card A : ℝ)⁻¹ • kronL A (trF ρ)) =
      (Fintype.card A : ℝ)⁻¹ • kronL A (trF (trF ρ)) := by
    rw [show trB ((Fintype.card A : ℝ)⁻¹ • kronL A (trF ρ)) =
        (Fintype.card A : ℝ)⁻¹ • trB (kronL A (trF ρ)) by
      ext x y; simp [trB, Finset.smul_sum], trB_kronL]
  rw [e2, hom_rsmul, smul_smul] at h
  set φ := (midH (A := A) (B := B) (C := C)).comp (kronL A)
  have hφ : ∀ N, midH (B := B) (kronL A N) = φ N := fun N => rfl
  rw [hφ] at h
  have hφC : (φ (trF (trF ρ))).PosDef := by
    rw [← hφ]; exact midH_posDef (kronL_posDef hρC)
  have hL := relEnt_hom (((Fintype.card B : ℝ))⁻¹ • midH (B := B) (trB ρ)) φ (trF (trF ρ)) hρC hφC
    (show 0 < (Fintype.card B : ℝ)⁻¹ * (Fintype.card A : ℝ)⁻¹ by positivity)
  rw [hL, hR] at h
  have k1 : ent (((Fintype.card B : ℝ))⁻¹ • midH (B := B) (trB ρ)) =
      - Real.log (Fintype.card B) + ent (trB ρ) := by
    rw [ent_hom _ _ hρAC (midH_posDef hρAC) (inv_pos.mpr hB), trace_midH, trace_midH, natmul_re,
      natmul_re, tAC, Real.log_inv, ent]
    field_simp
  have k2 : (trace (((Fintype.card B : ℝ))⁻¹ • midH (B := B) (trB ρ))).re = 1 := by
    rw [trace_smul_re, trace_midH, natmul_re, tAC]
    field_simp
  have k3 : (trace (((Fintype.card B : ℝ))⁻¹ • midH (B := B) (trB ρ) *
      φ (cfc Real.log (trF (trF ρ))))).re = ent (trF (trF ρ)) := by
    rw [smul_mul_assoc, trace_smul_re, ← hφ, ← map_mul, trace_midH, trace_mul_kronL, ent,
      trF_trB, natmul_re]
    field_simp
  have k4 : (trace (φ (trF (trF ρ)))).re = Fintype.card B * Fintype.card A := by
    rw [← hφ, trace_midH, trace_kronL, ← mul_assoc, ← Nat.cast_mul, natmul_re, tC]
    push_cast; ring
  rw [k1, k2, k3, k4] at h
  rw [Real.log_mul (inv_pos.mpr hB).ne' (inv_pos.mpr hA).ne', Real.log_inv, Real.log_inv] at h
  have e5 : ((Fintype.card B : ℝ)⁻¹ * (Fintype.card A : ℝ)⁻¹) *
      ((Fintype.card B : ℝ) * Fintype.card A) = 1 := by field_simp
  have e6 : (Fintype.card A : ℝ)⁻¹ * Fintype.card A = 1 := by field_simp
  unfold ent at *
  linarith

end three
end X6SSA


/-! X6 SSA library, part 4: strong subadditivity for arbitrary density matrices
(`QAlgorithms.vnEntropy`, bits), by continuity from the positive-definite case. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix MatrixOrder
noncomputable section
namespace X6SSA
open TroppMatrixConcentration Matrix Filter Topology

section gen
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Re tr (M log M)` through the functional calculus of `x log x`. -/
def Hn (M : Matrix n n ℂ) : ℝ := (trace (cfc (fun x : ℝ => x * Real.log x) M)).re

lemma Hn_posDef {M : Matrix n n ℂ} (hM : M.PosDef) : Hn M = ent M := by
  have hpos := hM.isStrictlyPositive
  unfold Hn ent
  rw [cfc_mul (fun x : ℝ => x) Real.log M (by fun_prop) (by
      refine Real.continuousOn_log.mono fun x hx => ?_
      have := hpos.spectrum_pos hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact this.ne')]
  congr 3
  exact cfc_id' ℝ M hM.isHermitian

lemma vn_eq (M : Matrix n n ℂ) : QAlgorithms.vnEntropy M = - Hn M / Real.log 2 := by
  unfold QAlgorithms.vnEntropy Hn
  have : (fun x : ℝ => x * Real.logb 2 x) = fun x => (Real.log 2)⁻¹ * (x * Real.log x) := by
    funext x; rw [Real.logb]; ring
  rw [this, cfc_const_mul (Real.log 2)⁻¹ (fun x : ℝ => x * Real.log x) M
    Real.continuous_mul_log.continuousOn, trace_smul_re]
  ring

lemma spec_density {M : Matrix n n ℂ} (hM : M.PosSemidef) (htr : M.trace = 1) :
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

lemma psd_rsmul {M : Matrix n n ℂ} (hM : M.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    (c • M).PosSemidef := by
  have : c • M = (c : ℂ) • M := by ext; simp [Complex.real_smul]
  rw [this]; exact hM.smul (by exact_mod_cast hc)

lemma cont_tr_re : Continuous fun M : Matrix n n ℂ => (trace M).re :=
  Complex.continuous_re.comp
    (LinearMap.continuous_of_finiteDimensional (traceLinearMap n ℂ ℂ))

lemma Hn_contOn : ContinuousOn (Hn : Matrix n n ℂ → ℝ)
    {a | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Set.Icc 0 1} :=
  cont_tr_re.comp_continuousOn
    (continuousOn_cfc (Matrix n n ℂ) isCompact_Icc _ Real.continuous_mul_log.continuousOn)

end gen

section ptr
variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

lemma trF_psd {M : Matrix (P × Q) (P × Q) ℂ} (hM : M.PosSemidef) : (trF M).PosSemidef := by
  rw [trF_eq]
  exact posSemidef_sum _ fun p _ => hM.conjTranspose_mul_mul_same _

lemma trF_lin (a b : ℝ) (X Y : Matrix (P × Q) (P × Q) ℂ) :
    trF (a • X + b • Y) = a • trF X + b • trF Y := by
  ext i j; simp [trF, Finset.sum_add_distrib, Finset.mul_sum, Complex.real_smul]

end ptr

section three
variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

lemma trB_psd {M : Matrix (A × (B × C)) (A × (B × C)) ℂ} (hM : M.PosSemidef) :
    (trB M).PosSemidef := by
  rw [trB_eq]; exact trF_psd (by rw [reindex_apply]; exact hM.submatrix _)

lemma trB_lin (a b : ℝ) (X Y : Matrix (A × (B × C)) (A × (B × C)) ℂ) :
    trB (a • X + b • Y) = a • trB X + b • trB Y := by
  ext i j; simp [trB, Finset.sum_add_distrib, Finset.mul_sum, Complex.real_smul]

lemma dens_ok {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} (hM : M.PosSemidef)
    (htr : M.trace = 1) : M ∈ {a : Matrix n n ℂ | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ Set.Icc 0 1} :=
  ⟨hM.1, spec_density hM htr⟩

/-- Strong subadditivity in the `Hn` form for every density matrix. -/
theorem ssa_Hn [Nonempty A] [Nonempty B] [Nonempty C]
    (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    Hn (trB ρ) - Hn (trF (trF ρ)) - Hn ρ + Hn (trF ρ) ≤ 0 := by
  set N : ℝ := (Fintype.card (A × (B × C)) : ℝ)
  have hN : 0 < N := by simp only [N]; exact_mod_cast Fintype.card_pos
  set E : Matrix (A × (B × C)) (A × (B × C)) ℂ := N⁻¹ • (1 : Matrix _ _ ℂ)
  have hE : E.PosDef := posDef_smul PosDef.one (inv_pos.mpr hN)
  have htrE : trace E = 1 := by
    rw [trace_smul, trace_one]; simp only [N]
    rw [Complex.real_smul]; push_cast
    field_simp
  let path : ℝ → Matrix (A × (B × C)) (A × (B × C)) ℂ := fun t => (1 - t) • ρ + t • E
  have tr_path : ∀ t, trace (path t) = 1 := by
    intro t
    simp only [path, trace_add, trace_smul, htr, htrE, Complex.real_smul]
    push_cast; ring
  have psd_path : ∀ t ∈ Set.Icc (0 : ℝ) 1, (path t).PosSemidef := by
    intro t ht
    refine PosSemidef.add ?_ ?_
    · exact psd_rsmul hρ (sub_nonneg.mpr ht.2)
    · exact psd_rsmul hE.posSemidef ht.1
  have pd_path : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (path t).PosDef := by
    intro t ht
    have h1 : ((1 - t) • ρ).PosSemidef := psd_rsmul hρ (sub_pos.mpr ht.2).le
    exact PosDef.posSemidef_add h1 (posDef_smul hE ht.1)
  let F : ℝ → ℝ := fun t =>
    Hn (trB (path t)) - Hn (trF (trF (path t))) - Hn (path t) + Hn (trF (path t))
  have hF : ∀ t ∈ Set.Ioo (0 : ℝ) 1, F t ≤ 0 := by
    intro t ht
    have hp := pd_path t ht
    have := ssa_posDef (path t) hp (tr_path t)
    simp only [F]
    rw [Hn_posDef (trB_posDef hp), Hn_posDef (trF_posDef (trF_posDef hp)), Hn_posDef hp,
      Hn_posDef (trF_posDef hp)]
    linarith
  -- continuity of `F` on `[0,1]`
  have c_path : Continuous path := by fun_prop
  have c1 : Continuous fun t => trB (path t) := by
    simp only [path, trB_lin]; fun_prop
  have c2 : Continuous fun t => trF (path t) := by
    simp only [path, trF_lin]; fun_prop
  have c3 : Continuous fun t => trF (trF (path t)) := by
    simp only [path, trF_lin]; fun_prop
  have tr1 : ∀ t, trace (trB (path t)) = 1 := fun t => by
    rw [trB_eq, trace_trF, trace_reind, tr_path]
  have tr2 : ∀ t, trace (trF (path t)) = 1 := fun t => by rw [trace_trF, tr_path]
  have tr3 : ∀ t, trace (trF (trF (path t))) = 1 := fun t => by rw [trace_trF, tr2]
  have hFc : ContinuousOn F (Set.Icc 0 1) := by
    refine ((((Hn_contOn.comp c1.continuousOn fun t ht =>
      dens_ok (trB_psd (psd_path t ht)) (tr1 t)).sub
      (Hn_contOn.comp c3.continuousOn fun t ht =>
      dens_ok (trF_psd (trF_psd (psd_path t ht))) (tr3 t))).sub
      (Hn_contOn.comp c_path.continuousOn fun t ht =>
      dens_ok (psd_path t ht) (tr_path t))).add
      (Hn_contOn.comp c2.continuousOn fun t ht =>
      dens_ok (trF_psd (psd_path t ht)) (tr2 t)))
  have hlim : Tendsto F (𝓝[>] 0) (𝓝 (F 0)) := by
    have := (hFc 0 ⟨le_rfl, zero_le_one⟩).mono_of_mem_nhdsWithin
      (show Set.Icc (0 : ℝ) 1 ∈ 𝓝[>] 0 from
        mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) Set.Ioo_subset_Icc_self)
    exact this
  have h0 : F 0 ≤ 0 := le_of_tendsto hlim
    (mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) fun t ht => hF t ht)
  have hp0 : path 0 = ρ := by simp [path]
  simpa only [F, hp0] using h0

/-- Strong subadditivity `S(AC) + S(BC) - S(C) - S(ABC) ≥ 0` (von Neumann entropy in bits) for
every density matrix on `A × (B × C)`. -/
theorem ssa [Nonempty A] [Nonempty B] [Nonempty C]
    (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    0 ≤ QAlgorithms.vnEntropy (trB ρ) + QAlgorithms.vnEntropy (trF ρ) -
      QAlgorithms.vnEntropy (trF (trF ρ)) - QAlgorithms.vnEntropy ρ := by
  have h := ssa_Hn ρ hρ htr
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  simp only [vn_eq]
  rw [show -Hn (trB ρ) / Real.log 2 + -Hn (trF ρ) / Real.log 2 - -Hn (trF (trF ρ)) / Real.log 2 -
      -Hn ρ / Real.log 2 = -(Hn (trB ρ) - Hn (trF (trF ρ)) - Hn ρ + Hn (trF ρ)) / Real.log 2 by ring]
  exact div_nonneg (by linarith) hl.le

end three
end X6SSA


/-! X6 SSA library, part 5: reindexing invariance of `vnEntropy` and strong subadditivity
conditioned on the middle factor, `S(AB) + S(BC) - S(B) - S(ABC) ≥ 0`. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix
noncomputable section
namespace X6SSA
open TroppMatrixConcentration Matrix

lemma vn_reind {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (M : Matrix m m ℂ) (hM : M.IsHermitian) :
    QAlgorithms.vnEntropy (reindex e e M) = QAlgorithms.vnEntropy M := by
  unfold QAlgorithms.vnEntropy
  have h := map_cfc_mat (reind e) (fun x : ℝ => x * Real.logb 2 x) M hM
  simp only [reind_apply] at h
  rw [← h, trace_reind]

section three
variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

/-- trace out the last factor. -/
def trC (M : Matrix (A × (B × C)) (A × (B × C)) ℂ) : Matrix (A × B) (A × B) ℂ :=
  of fun i j => ∑ k, M (i.1, (i.2, k)) (j.1, (j.2, k))

/-- trace out the second factor of a pair. -/
def trR {P Q : Type*} [Fintype Q] (M : Matrix (P × Q) (P × Q) ℂ) : Matrix P P ℂ :=
  of fun i j => ∑ k, M (i, k) (j, k)

/-- `A × (B × C) ≃ A × (C × B)`. -/
def swBC : A × (B × C) ≃ A × (C × B) where
  toFun x := (x.1, (x.2.2, x.2.1))
  invFun y := (y.1, (y.2.2, y.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Strong subadditivity conditioned on the middle factor. -/
theorem ssa_mid [Nonempty A] [Nonempty B] [Nonempty C]
    (ρ : Matrix (A × (B × C)) (A × (B × C)) ℂ) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    0 ≤ QAlgorithms.vnEntropy (trC ρ) + QAlgorithms.vnEntropy (trF ρ) -
      QAlgorithms.vnEntropy (trR (trF ρ)) - QAlgorithms.vnEntropy ρ := by
  set τ := reindex (swBC (A := A) (B := B) (C := C)) swBC ρ
  have hτ : τ.PosSemidef := by simp only [τ, reindex_apply]; exact hρ.submatrix _
  have htτ : trace τ = 1 := by simp only [τ]; rw [trace_reind, htr]
  have h := ssa τ hτ htτ
  have e1 : trB τ = trC ρ := by ext i j; rfl
  have e2 : trF τ = reindex (Equiv.prodComm B C) (Equiv.prodComm B C) (trF ρ) := by ext i j; rfl
  have e3 : trF (trF τ) = trR (trF ρ) := by ext i j; rfl
  rw [e1, e3, e2, vn_reind _ _ (trF_psd hρ).1] at h
  simp only [τ] at h
  rw [vn_reind _ _ hρ.1] at h
  exact h

end three
end X6SSA


/-! X6 SSA library, part 6: subadditivity `S(AB) ≤ S(A) + S(B)`. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix
noncomputable section
namespace X6SSA
open TroppMatrixConcentration Matrix

lemma vn_one {u : Type*} [Fintype u] [DecidableEq u] : QAlgorithms.vnEntropy (1 : Matrix u u ℂ) = 0 := by
  unfold QAlgorithms.vnEntropy
  rw [show (1 : Matrix u u ℂ) = algebraMap ℝ (Matrix u u ℂ) 1 from (map_one _).symm,
    cfc_algebraMap]
  simp

/-- `ι × κ ≃ ι × (κ × Unit)`. -/
def addU {ι κ : Type*} : ι × κ ≃ ι × (κ × Unit) where
  toFun x := (x.1, (x.2, ()))
  invFun y := (y.1, y.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- `ι ≃ ι × Unit`. -/
def addU1 {ι : Type*} : ι ≃ ι × Unit where
  toFun x := (x, ())
  invFun y := y.1
  left_inv _ := rfl
  right_inv _ := rfl

/-- Subadditivity of von Neumann entropy (bits). -/
theorem subadd {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Nonempty ι] [Nonempty κ] (ρ : Matrix (ι × κ) (ι × κ) ℂ) (hρ : ρ.PosSemidef)
    (htr : trace ρ = 1) :
    QAlgorithms.vnEntropy ρ ≤ QAlgorithms.vnEntropy (trR ρ) + QAlgorithms.vnEntropy (trF ρ) := by
  set τ := reindex (addU (ι := ι) (κ := κ)) addU ρ
  have hτ : τ.PosSemidef := by simp only [τ, reindex_apply]; exact hρ.submatrix _
  have htτ : trace τ = 1 := by simp only [τ]; rw [trace_reind, htr]
  have h := ssa τ hτ htτ
  have e1 : trB τ = reindex addU1 addU1 (trR ρ) := by ext i j; rfl
  have e2 : trF τ = reindex addU1 addU1 (trF ρ) := by ext i j; rfl
  have e3 : trF (trF τ) = 1 := by
    ext i j
    have : trF (trF τ) i j = trace ρ := by
      simp only [trF, of_apply, τ, reindex_apply, submatrix_apply, trace, diag_apply,
        Fintype.sum_prod_type]
      exact Finset.sum_comm
    rw [this, htr]; simp [one_apply]
  have hR : (trR ρ).IsHermitian := by
    have := trB_psd (B := κ) hτ
    rw [show trB τ = reindex addU1 addU1 (trR ρ) from e1] at this
    have h2 := this.1.submatrix addU1
    simpa [reindex_apply] using h2
  rw [e3, e1, e2, vn_one, vn_reind _ _ hR, vn_reind _ _ (trF_psd hρ).1] at h
  simp only [τ] at h
  rw [vn_reind _ _ hρ.1] at h
  linarith

end X6SSA


/-! X6 SSA library, part 7: marginals along abstract coordinate splittings `Ω ≃ K × F`, their
comparison, and strong subadditivity for a four-part splitting `Ω ≃ (A × (B × C)) × D`. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix
noncomputable section
namespace X6SSA
open TroppMatrixConcentration Matrix

/-- marginal on `K` along a splitting `Φ : Ω ≃ K × F`. -/
def marg {Ω K F : Type*} [Fintype F] (Φ : Ω ≃ K × F) (ρ : Matrix Ω Ω ℂ) : Matrix K K ℂ :=
  trR (reindex Φ Φ ρ)

lemma marg_psd {Ω K F : Type*} [Fintype F] [Fintype K] [DecidableEq K] [DecidableEq F]
    (Φ : Ω ≃ K × F) {ρ : Matrix Ω Ω ℂ} (hρ : ρ.PosSemidef) : (marg Φ ρ).PosSemidef := by
  have h : marg Φ ρ = trF (reindex (Φ.trans (Equiv.prodComm K F)) (Φ.trans (Equiv.prodComm K F)) ρ) := by
    ext i j; rfl
  rw [h]; exact trF_psd (by rw [reindex_apply]; exact hρ.submatrix _)

lemma marg_trace {Ω K F : Type*} [Fintype Ω] [Fintype F] [Fintype K]
    (Φ : Ω ≃ K × F) (ρ : Matrix Ω Ω ℂ) : trace (marg Φ ρ) = trace ρ := by
  classical
  have h : trace (marg Φ ρ) = trace (reindex Φ Φ ρ) := by
    simp only [marg, trR, trace, diag_apply, of_apply, Fintype.sum_prod_type]
  rw [h, trace_reind]

/-- Two splittings that keep the same information give the same marginal up to reindexing. -/
lemma marg_transport {Ω K₁ F₁ K₂ F₂ : Type*} [Fintype F₁] [Fintype F₂]
    (Φ₁ : Ω ≃ K₁ × F₁) (Φ₂ : Ω ≃ K₂ × F₂) [Nonempty K₁] [Nonempty F₁]
    (h1 : ∀ ω ω', (Φ₁ ω).1 = (Φ₁ ω').1 ↔ (Φ₂ ω).1 = (Φ₂ ω').1)
    (h2 : ∀ ω ω', (Φ₁ ω).2 = (Φ₁ ω').2 ↔ (Φ₂ ω).2 = (Φ₂ ω').2) (ρ : Matrix Ω Ω ℂ) :
    ∃ κ : K₁ ≃ K₂, marg Φ₂ ρ = reindex κ κ (marg Φ₁ ρ) := by
  obtain ⟨k0⟩ := ‹Nonempty K₁›
  obtain ⟨z0⟩ := ‹Nonempty F₁›
  let f : K₁ → K₂ := fun k => (Φ₂ (Φ₁.symm (k, z0))).1
  let g : F₁ → F₂ := fun z => (Φ₂ (Φ₁.symm (k0, z))).2
  have kf : ∀ ω, (Φ₂ ω).1 = f (Φ₁ ω).1 := by
    intro ω
    refine ((h1 _ _).mp ?_).symm
    simp
  have kg : ∀ ω, (Φ₂ ω).2 = g (Φ₁ ω).2 := by
    intro ω
    refine ((h2 _ _).mp ?_).symm
    simp
  have fb : Function.Bijective f := by
    constructor
    · intro k k' hk
      have := (h1 (Φ₁.symm (k, z0)) (Φ₁.symm (k', z0))).mpr hk
      simpa using this
    · intro k₂
      have hF₂ : Nonempty F₂ := ⟨(Φ₂ (Φ₁.symm (k0, z0))).2⟩
      obtain ⟨z2⟩ := hF₂
      refine ⟨(Φ₁ (Φ₂.symm (k₂, z2))).1, ?_⟩
      rw [← kf]; simp
  have gb : Function.Bijective g := by
    constructor
    · intro z z' hz
      have := (h2 (Φ₁.symm (k0, z)) (Φ₁.symm (k0, z'))).mpr hz
      simpa using this
    · intro z₂
      obtain ⟨k2⟩ : Nonempty K₂ := ⟨f k0⟩
      refine ⟨(Φ₁ (Φ₂.symm (k2, z₂))).2, ?_⟩
      rw [← kg]; simp
  let κ := Equiv.ofBijective f fb
  let lam := Equiv.ofBijective g gb
  have key : ∀ k z, Φ₂.symm (κ k, lam z) = Φ₁.symm (k, z) := by
    intro k z
    apply Φ₂.injective
    rw [Equiv.apply_symm_apply, Prod.ext_iff, kf, kg]
    simp [κ, lam]
  refine ⟨κ, ?_⟩
  ext x y
  simp only [marg, trR, reindex_apply, submatrix_apply, of_apply]
  rw [← Equiv.sum_comp lam]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hx : x = κ (κ.symm x) := (κ.apply_symm_apply x).symm
  have hy : y = κ (κ.symm y) := (κ.apply_symm_apply y).symm
  conv_lhs => rw [hx, hy, key, key]

lemma vn_marg_eq {Ω K₁ F₁ K₂ F₂ : Type*} [Fintype F₁] [Fintype F₂] [Fintype K₁] [Fintype K₂]
    [DecidableEq K₁] [DecidableEq K₂] [DecidableEq F₁]
    (Φ₁ : Ω ≃ K₁ × F₁) (Φ₂ : Ω ≃ K₂ × F₂) [Nonempty K₁] [Nonempty F₁]
    (h1 : ∀ ω ω', (Φ₁ ω).1 = (Φ₁ ω').1 ↔ (Φ₂ ω).1 = (Φ₂ ω').1)
    (h2 : ∀ ω ω', (Φ₁ ω).2 = (Φ₁ ω').2 ↔ (Φ₂ ω).2 = (Φ₂ ω').2) {ρ : Matrix Ω Ω ℂ}
    (hρ : ρ.PosSemidef) :
    QAlgorithms.vnEntropy (marg Φ₂ ρ) = QAlgorithms.vnEntropy (marg Φ₁ ρ) := by
  obtain ⟨κ, hκ⟩ := marg_transport Φ₁ Φ₂ h1 h2 ρ
  rw [hκ, vn_reind _ _ (marg_psd Φ₁ hρ).1]

section four
variable {A B C D : Type*}

def r21 : (A × (B × C)) × D ≃ (A × C) × (B × D) where
  toFun x := ((x.1.1, x.1.2.2), (x.1.2.1, x.2))
  invFun y := ((y.1.1, (y.2.1, y.1.2)), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def r31 : (A × (B × C)) × D ≃ (B × C) × (A × D) where
  toFun x := (x.1.2, (x.1.1, x.2))
  invFun y := ((y.2.1, y.1), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def r1 : (A × (B × C)) × D ≃ C × ((A × B) × D) where
  toFun x := (x.1.2.2, ((x.1.1, x.1.2.1), x.2))
  invFun y := ((y.2.1.1, (y.2.1.2, y.1)), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype D] [DecidableEq D]

/-- SSA for a four-part splitting: `S(AC) + S(BC) - S(C) - S(ABC) ≥ 0`, the `D` part discarded. -/
theorem ssa_split {Ω : Type*} [Fintype Ω] [Nonempty A] [Nonempty B] [Nonempty C]
    (Φ : Ω ≃ (A × (B × C)) × D) (ρ : Matrix Ω Ω ℂ) (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    0 ≤ QAlgorithms.vnEntropy (marg (Φ.trans r21) ρ) +
      QAlgorithms.vnEntropy (marg (Φ.trans r31) ρ) -
      QAlgorithms.vnEntropy (marg (Φ.trans r1) ρ) - QAlgorithms.vnEntropy (marg Φ ρ) := by
  have h := ssa (marg Φ ρ) (marg_psd Φ hρ) (by rw [marg_trace, htr])
  have e1 : trB (marg Φ ρ) = marg (Φ.trans r21) ρ := by
    ext i j
    simp only [trB, marg, trR, reindex_apply, submatrix_apply, of_apply, Fintype.sum_prod_type]
    rfl
  have e2 : trF (marg Φ ρ) = marg (Φ.trans r31) ρ := by
    ext i j
    simp only [trF, marg, trR, reindex_apply, submatrix_apply, of_apply, Fintype.sum_prod_type]
    rfl
  have e3 : trF (trF (marg Φ ρ)) = marg (Φ.trans r1) ρ := by
    ext i j
    simp only [trF, marg, trR, reindex_apply, submatrix_apply, of_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    rfl
  rw [e3, e1, e2] at h
  exact h

end four
end X6SSA


/-! X6 SSA library, part 8: `S(M Mᴴ) = S(Mᴴ M)` for rectangular `M`, hence complementary
marginals of a pure state have equal entropy. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix
noncomputable section
namespace X6SSA
open Matrix Polynomial

lemma roots_prod {κ : Type*} [Fintype κ] (ν : κ → ℂ) :
    (∏ j, (X - C (ν j))).roots = Multiset.map ν Finset.univ.val := by
  rw [Finset.prod_eq_multiset_prod]
  have : Multiset.map (fun j => X - C (ν j)) Finset.univ.val =
      Multiset.map (fun a => X - C a) (Multiset.map ν Finset.univ.val) := by
    rw [Multiset.map_map]; rfl
  rw [this, Polynomial.roots_multiset_prod_X_sub_C]

lemma sum_of_prod_eq {κ κ' : Type*} [Fintype κ] [Fintype κ'] (ν : κ → ℂ) (ν' : κ' → ℂ)
    (h : ∏ j, (X - C (ν j)) = ∏ j, (X - C (ν' j))) (g : ℂ → ℝ) :
    ∑ j, g (ν j) = ∑ j, g (ν' j) := by
  have h1 := congrArg Polynomial.roots h
  rw [roots_prod, roots_prod] at h1
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
  have a1 : Multiset.map (fun j => g (ν j)) Finset.univ.val =
      Multiset.map g (Multiset.map ν Finset.univ.val) := by rw [Multiset.map_map]; rfl
  have a2 : Multiset.map (fun j => g (ν' j)) Finset.univ.val =
      Multiset.map g (Multiset.map ν' Finset.univ.val) := by rw [Multiset.map_map]; rfl
  rw [a1, a2, h1]

lemma vn_eig {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    QAlgorithms.vnEntropy A = ∑ i, -(hA.eigenvalues i * Real.logb 2 (hA.eigenvalues i)) := by
  unfold QAlgorithms.vnEntropy
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, one_mul, Matrix.trace_diagonal,
    Complex.re_sum, ← Finset.sum_neg_distrib]
  simp

/-- `S(M Mᴴ) = S(Mᴴ M)`. -/
theorem vn_mul_conj {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) : QAlgorithms.vnEntropy (M * Mᴴ) = QAlgorithms.vnEntropy (Mᴴ * M) := by
  have hP : (M * Mᴴ).IsHermitian := isHermitian_mul_conjTranspose_self M
  have hQ : (Mᴴ * M).IsHermitian := isHermitian_conjTranspose_mul_self M
  rw [vn_eig hP, vn_eig hQ]
  let g : ℂ → ℝ := fun z => -(z.re * Real.logb 2 z.re)
  let ν : Fin (Fintype.card n) ⊕ m → ℂ := Sum.elim (fun _ => 0) fun i => (hP.eigenvalues i : ℂ)
  let ν' : Fin (Fintype.card m) ⊕ n → ℂ := Sum.elim (fun _ => 0) fun i => (hQ.eigenvalues i : ℂ)
  have hprod : ∏ j, (X - C (ν j)) = ∏ j, (X - C (ν' j)) := by
    simp only [ν, ν', Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, map_zero, sub_zero,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have e1 := hP.charpoly_eq
    have e2 := hQ.charpoly_eq
    have := charpoly_mul_comm' Mᴴ M
    have c1 : (∏ i, (X - C ((hP.eigenvalues i : ℝ) : ℂ))) = (M * Mᴴ).charpoly := by
      rw [e1]; rfl
    have c2 : (∏ i, (X - C ((hQ.eigenvalues i : ℝ) : ℂ))) = (Mᴴ * M).charpoly := by
      rw [e2]; rfl
    rw [c1, c2]
    exact this.symm
  have := sum_of_prod_eq ν ν' hprod g
  simp only [ν, ν', g, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Complex.zero_re,
    zero_mul, neg_zero, Finset.sum_const_zero, zero_add, Complex.ofReal_re] at this
  exact this

lemma vn_transpose {n : Type*} [Fintype n] [DecidableEq n] {N : Matrix n n ℂ}
    (hN : N.IsHermitian) : QAlgorithms.vnEntropy Nᵀ = QAlgorithms.vnEntropy N := by
  have hT : Nᵀ.IsHermitian := hN.transpose
  rw [vn_eig hT, vn_eig hN]
  have hprod : ∏ j, (X - C ((hT.eigenvalues j : ℝ) : ℂ)) = ∏ j, (X - C ((hN.eigenvalues j : ℝ) : ℂ)) := by
    have e1 := hT.charpoly_eq
    have e2 := hN.charpoly_eq
    have c1 : (∏ i, (X - C ((hT.eigenvalues i : ℝ) : ℂ))) = Nᵀ.charpoly := by rw [e1]; rfl
    have c2 : (∏ i, (X - C ((hN.eigenvalues i : ℝ) : ℂ))) = N.charpoly := by rw [e2]; rfl
    rw [c1, c2, charpoly_transpose]
  have := sum_of_prod_eq _ _ hprod (fun z => -(z.re * Real.logb 2 z.re))
  simpa using this

/-- complementary marginals of a pure state have equal entropy. -/
theorem vn_pure_marginals {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (ψ : EuclideanSpace ℂ (m × n)) :
    QAlgorithms.vnEntropy (trR (QAlgorithms.pureDensity ψ)) =
      QAlgorithms.vnEntropy (trF (QAlgorithms.pureDensity ψ)) := by
  let M : Matrix m n ℂ := of fun x y => ψ (x, y)
  have e1 : trR (QAlgorithms.pureDensity ψ) = M * Mᴴ := by
    ext x x'; simp [trR, QAlgorithms.pureDensity, M, mul_apply]
  have e2 : trF (QAlgorithms.pureDensity ψ) = (Mᴴ * M)ᵀ := by
    ext y y'; simp [trF, QAlgorithms.pureDensity, M, mul_apply, mul_comm]
  rw [e1, e2, vn_transpose (isHermitian_conjTranspose_mul_self M), vn_mul_conj]

end X6SSA


/-! X6 channel library, part 1: entropies of complementary marginals of pure states along
abstract splittings, subadditivity along splittings, and the two-channel Stinespring vector
`lam Ψ E F` on `R × (C × (L × K))` with its marginals. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
noncomputable section
namespace X6CH
open Matrix X6SSA QAlgorithms

section gen
variable {Ω X Y Z : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

lemma pd_psd {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) : (pureDensity v).PosSemidef := by
  have : pureDensity v = Matrix.vecMulVec (v : ι → ℂ) (star (v : ι → ℂ)) := by
    ext i j; simp [pureDensity, Matrix.vecMulVec_apply]
  rw [this]; exact Matrix.posSemidef_vecMulVec_self_star _

omit [Fintype Ω] [DecidableEq Ω] in
/-- complementary marginals of a pure state along a splitting have equal entropy. -/
lemma pure_comp (Φ : Ω ≃ X × Y) (w : EuclideanSpace ℂ Ω) :
    vnEntropy (marg Φ (pureDensity w)) =
      vnEntropy (marg (Φ.trans (Equiv.prodComm X Y)) (pureDensity w)) := by
  let v : EuclideanSpace ℂ (X × Y) := WithLp.toLp 2 fun p => w (Φ.symm p)
  have e1 : marg Φ (pureDensity w) = trR (pureDensity v) := by
    ext i j; simp [marg, trR, pureDensity, v, reindex_apply]
  have e2 : marg (Φ.trans (Equiv.prodComm X Y)) (pureDensity w) = trF (pureDensity v) := by
    ext i j; simp [marg, trR, trF, pureDensity, v, reindex_apply]
  rw [e1, e2, vn_pure_marginals]

def rX : (X × Y) × Z ≃ X × (Y × Z) := Equiv.prodAssoc X Y Z

def rY : (X × Y) × Z ≃ Y × (X × Z) where
  toFun p := (p.1.2, (p.1.1, p.2))
  invFun q := ((q.2.1, q.1), q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- subadditivity along a splitting `Ω ≃ (X × Y) × Z`. -/
lemma subadd_split [Nonempty X] [Nonempty Y] (Φ : Ω ≃ (X × Y) × Z) (ρ : Matrix Ω Ω ℂ)
    (hρ : ρ.PosSemidef) (htr : trace ρ = 1) :
    vnEntropy (marg Φ ρ) ≤ vnEntropy (marg (Φ.trans rX) ρ) + vnEntropy (marg (Φ.trans rY) ρ) := by
  have h := subadd (marg Φ ρ) (marg_psd Φ hρ) (by rw [marg_trace, htr])
  have e1 : trR (marg Φ ρ) = marg (Φ.trans rX) ρ := by
    ext i j
    simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, Fintype.sum_prod_type]
    rfl
  have e2 : trF (marg Φ ρ) = marg (Φ.trans rY) ρ := by
    ext i j
    simp only [trF, marg, trR, reindex_apply, submatrix_apply, of_apply, Fintype.sum_prod_type]
    rfl
  rw [e1, e2] at h
  exact h

lemma pd_trace {ι : Type*} [Fintype ι] (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    (pureDensity v).trace = 1 := by
  have h := EuclideanSpace.norm_sq_eq v
  rw [hv] at h
  simp only [Matrix.trace, Matrix.diag_apply, pureDensity, Matrix.of_apply, Complex.mul_conj]
  have : ∑ i, ((Complex.normSq (v i) : ℝ) : ℂ) = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [this, ← h]; simp

end gen

section kraus
variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

lemma kraus_rank1 {K : Type*} [Fintype K] (E : K → Matrix B A ℂ) (u v : A → ℂ) :
    krausApply E (vecMulVec u (star v)) = ∑ k, vecMulVec (E k *ᵥ u) (star (E k *ᵥ v)) := by
  unfold krausApply
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]

lemma kraus_sum {K ι : Type*} [Fintype K] (E : K → Matrix B A ℂ) (s : Finset ι)
    (X : ι → Matrix A A ℂ) : krausApply E (∑ i ∈ s, X i) = ∑ i ∈ s, krausApply E (X i) := by
  show ∑ j, E j * (∑ i ∈ s, X i) * (E j)ᴴ = ∑ i ∈ s, ∑ j, E j * X i * (E j)ᴴ
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_comm

end kraus

end X6CH


/-! X6 channel library, part 2: the two-channel Stinespring vector and its marginals. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
noncomputable section
namespace X6CH
open Matrix X6SSA QAlgorithms

variable {R A B C K L : Type*} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L]

/-- `ψ(r, a) = Ψ a r`. -/
def vecOf (Ψ : Matrix A R ℂ) : EuclideanSpace ℂ (R × A) := WithLp.toLp 2 fun p => Ψ p.2 p.1

/-- the Stinespring vector of `F ∘ E` applied to `vecOf Ψ`, environments `L` (for `F`) and `K`. -/
def lam (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ) :
    EuclideanSpace ℂ (R × (C × (L × K))) :=
  WithLp.toLp 2 fun x => (F x.2.2.1 * E x.2.2.2 * Ψ) x.2.1 x.1

/-- complementary-channel output `(k, k') ↦ tr(E_k σ E_k'ᴴ)`. -/
def comp (E : K → Matrix B A ℂ) (σ : Matrix A A ℂ) : Matrix K K ℂ :=
  of fun k k' => trace (E k * σ * (E k')ᴴ)

/-- Stinespring isometry of a Kraus family. -/
def stV (F : L → Matrix C B ℂ) : Matrix (C × L) B ℂ := of fun p b => F p.2 p.1 b

def sRC : R × (C × (L × K)) ≃ (R × C) × (L × K) where
  toFun x := ((x.1, x.2.1), x.2.2)
  invFun y := (y.1.1, (y.1.2, y.2))
  left_inv _ := rfl
  right_inv _ := rfl

def sC : R × (C × (L × K)) ≃ C × (R × (L × K)) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun y := (y.2.1, (y.1, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

def sL : R × (C × (L × K)) ≃ L × (R × (C × K)) where
  toFun x := (x.2.2.1, (x.1, (x.2.1, x.2.2.2)))
  invFun y := (y.2.1, (y.2.2.1, (y.1, y.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

def sK : R × (C × (L × K)) ≃ K × (R × (C × L)) where
  toFun x := (x.2.2.2, (x.1, (x.2.1, x.2.2.1)))
  invFun y := (y.2.1, (y.2.2.1, (y.2.2.2, y.1)))
  left_inv _ := rfl
  right_inv _ := rfl

def sCL : R × (C × (L × K)) ≃ (C × L) × (R × K) where
  toFun x := ((x.2.1, x.2.2.1), (x.1, x.2.2.2))
  invFun y := (y.2.1, (y.1.1, (y.1.2, y.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

lemma mulVec_col (M : Matrix C A ℂ) (Ψ : Matrix A R ℂ) (r : R) :
    (M *ᵥ fun a => Ψ a r) = fun c => (M * Ψ) c r := by
  ext c; simp [mulVec, dotProduct, mul_apply]

lemma gram (Ψ : Matrix A R ℂ) :
    Ψ * Ψᴴ = ∑ r, vecMulVec (fun a => Ψ a r) (star fun a => Ψ a r) := by
  ext a a'; simp [mul_apply, Matrix.sum_apply, vecMulVec_apply]

lemma conj_eq (z : ℂ) : star z = conj z := rfl

lemma trace_mul_conjT {P Q : Type*} [Fintype P] [Fintype Q] (X Y : Matrix P Q ℂ) :
    trace (X * Yᴴ) = ∑ p, ∑ q, X p q * conj (Y p q) := by
  simp [trace, mul_apply, conjTranspose_apply, conj_eq]

lemma mul_conjT_apply {P P' Q : Type*} [Fintype Q] (X : Matrix P Q ℂ) (Y : Matrix P' Q ℂ)
    (p : P) (p' : P') : (X * Yᴴ) p p' = ∑ q, X p q * conj (Y p' q) := by
  simp [mul_apply, conjTranspose_apply, conj_eq]

lemma sum3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

/-- the `C` marginal is the output `F(E(ΨΨᴴ))`. -/
lemma m_C (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ) :
    marg sC (pureDensity (lam Ψ E F)) = krausApply F (krausApply E (Ψ * Ψᴴ)) := by
  rw [gram, kraus_sum]
  simp only [kraus_rank1, kraus_sum, mulVec_mulVec, mulVec_col]
  ext c c'
  simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, pureDensity, lam, sC,
    Equiv.coe_fn_symm_mk, Matrix.sum_apply, vecMulVec_apply, Fintype.sum_prod_type, Pi.star_apply,
    conj_eq, Matrix.mul_assoc]
  refine Finset.sum_congr rfl fun r _ => ?_
  exact Finset.sum_comm

/-- the `L × K`-free (`R × C`) marginal is `id ⊗ F` after `id ⊗ E`. -/
lemma m_RC (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ) :
    marg sRC (pureDensity (lam Ψ E F)) =
      idTensorSuperop (krausApply F) (idTensorSuperop (krausApply E) (pureDensity (vecOf Ψ))) := by
  ext ⟨r, c⟩ ⟨r', c'⟩
  have h1 : (of fun i i' => (idTensorSuperop (krausApply E) (pureDensity (vecOf Ψ))) (r, i) (r', i'))
      = krausApply E (vecMulVec (fun a => Ψ a r) (star fun a => Ψ a r')) := by
    ext b b'
    simp only [idTensorSuperop, of_apply]
    congr 2
  simp only [idTensorSuperop, of_apply] at h1 ⊢
  rw [h1, kraus_rank1, kraus_sum]
  simp only [kraus_rank1, mulVec_mulVec, mulVec_col]
  simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, pureDensity, lam, sRC,
    Equiv.coe_fn_symm_mk, Matrix.sum_apply, vecMulVec_apply, Fintype.sum_prod_type, Pi.star_apply,
    conj_eq, Matrix.mul_assoc]
  exact Finset.sum_comm

/-- the `K` marginal is the complementary output of `E`. -/
lemma m_K (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ)
    (hF : ∑ l, (F l)ᴴ * F l = 1) :
    marg sK (pureDensity (lam Ψ E F)) = comp E (Ψ * Ψᴴ) := by
  ext k k'
  have key : trace (E k * (Ψ * Ψᴴ) * (E k')ᴴ) =
      ∑ l, trace ((F l * E k * Ψ) * (F l * E k' * Ψ)ᴴ) := by
    have : ∀ l, trace ((F l * E k * Ψ) * (F l * E k' * Ψ)ᴴ) =
        trace ((F l)ᴴ * F l * (E k * (Ψ * Ψᴴ) * (E k')ᴴ)) := by
      intro l
      rw [show F l * E k * Ψ * (F l * E k' * Ψ)ᴴ = (F l * (E k * (Ψ * Ψᴴ) * (E k')ᴴ)) * (F l)ᴴ by
        simp only [conjTranspose_mul, Matrix.mul_assoc], trace_mul_comm]
      simp only [Matrix.mul_assoc]
    simp only [this, ← trace_sum, ← Matrix.sum_mul, hF, Matrix.one_mul]
  rw [comp, of_apply, key]
  simp only [trace_mul_conjT]
  simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, pureDensity, lam, sK,
    Equiv.coe_fn_symm_mk, Fintype.sum_prod_type]
  exact sum3 _

/-- the `L` marginal is the complementary output of `F` on `E(ΨΨᴴ)`. -/
lemma m_L (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ) :
    marg sL (pureDensity (lam Ψ E F)) = comp F (krausApply E (Ψ * Ψᴴ)) := by
  ext l l'
  have key : trace (F l * krausApply E (Ψ * Ψᴴ) * (F l')ᴴ) =
      ∑ k, trace ((F l * E k * Ψ) * (F l' * E k * Ψ)ᴴ) := by
    show trace (F l * (∑ j, E j * (Ψ * Ψᴴ) * (E j)ᴴ) * (F l')ᴴ) = _
    simp only [Matrix.mul_sum, Matrix.sum_mul, trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [comp, of_apply, key]
  simp only [trace_mul_conjT]
  simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, pureDensity, lam, sL,
    Equiv.coe_fn_symm_mk, Fintype.sum_prod_type]
  exact sum3 _

/-- the `C × L` marginal is the Stinespring image of `E(ΨΨᴴ)`. -/
lemma m_CL (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ) :
    marg sCL (pureDensity (lam Ψ E F)) = stV F * krausApply E (Ψ * Ψᴴ) * (stV F)ᴴ := by
  have hG : ∀ k, stV F * E k * Ψ = of fun (p : C × L) r => (F p.2 * E k * Ψ) p.1 r := by
    intro k; ext p r; simp [stV, mul_apply, Finset.sum_mul, Matrix.mul_assoc]
  have e : stV F * krausApply E (Ψ * Ψᴴ) * (stV F)ᴴ =
      ∑ k, (stV F * E k * Ψ) * (stV F * E k * Ψ)ᴴ := by
    show stV F * (∑ j, E j * (Ψ * Ψᴴ) * (E j)ᴴ) * (stV F)ᴴ = _
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e]
  simp only [hG]
  ext p p'
  simp only [Matrix.sum_apply, mul_conjT_apply, of_apply]
  simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, pureDensity, lam, sCL,
    Equiv.coe_fn_symm_mk, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- the `R` marginal. -/
lemma m_R (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ)
    (hE : ∑ k, (E k)ᴴ * E k = 1) (hF : ∑ l, (F l)ᴴ * F l = 1) :
    marg (Equiv.refl _) (pureDensity (lam Ψ E F)) = (Ψᴴ * Ψ)ᵀ := by
  have e : Ψᴴ * Ψ = ∑ l, ∑ k, (F l * E k * Ψ)ᴴ * (F l * E k * Ψ) := by
    have : ∀ l k, (F l * E k * Ψ)ᴴ * (F l * E k * Ψ) = Ψᴴ * ((E k)ᴴ * ((F l)ᴴ * F l) * E k) * Ψ := by
      intro l k; simp only [conjTranspose_mul, Matrix.mul_assoc]
    simp only [this]
    rw [Finset.sum_comm]
    simp only [← Matrix.sum_mul, ← Matrix.mul_sum, hF, Matrix.mul_one, hE]
  rw [e]
  ext r r'
  simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, pureDensity, lam,
    Equiv.refl_symm, Equiv.refl_apply, Fintype.sum_prod_type, Matrix.sum_apply, mul_apply,
    conjTranspose_apply, conj_eq, transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end X6CH


/-! X6 channel library, part 3: isometric invariance, the entropy of `id ⊗ E` on a pure state
equals the entropy of the complementary output, and the four entropy inequalities of the
two-channel Stinespring state. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CH
open Matrix X6SSA QAlgorithms

/-- isometric invariance of the entropy. -/
lemma vn_iso {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) (X : Matrix n n ℂ) (hX : X.PosSemidef) :
    vnEntropy (V * X * Vᴴ) = vnEntropy X := by
  open scoped MatrixOrder in
  have h0 : (0 : Matrix n n ℂ) ≤ X := Matrix.nonneg_iff_posSemidef.mpr hX
  open scoped MatrixOrder in
  have hs : (CFC.sqrt X)ᴴ = CFC.sqrt X :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg X)).isHermitian.eq
  open scoped MatrixOrder in
  have hX' : X = CFC.sqrt X * CFC.sqrt X := (CFC.sqrt_mul_sqrt_self X h0).symm
  set s := CFC.sqrt X
  have e1 : V * X * Vᴴ = (V * s) * (V * s)ᴴ := by
    rw [conjTranspose_mul, hs]; conv_lhs => rw [hX']
    simp only [Matrix.mul_assoc]
  have e2 : (V * s)ᴴ * (V * s) = X := by
    rw [conjTranspose_mul, hs, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul, ← hX']
  rw [e1, vn_mul_conj, e2]

lemma kraus_psd {A B K : Type*} [Fintype A] [Fintype B] [Fintype K] (E : K → Matrix B A ℂ)
    {X : Matrix A A ℂ} (hX : X.PosSemidef) : (krausApply E X).PosSemidef :=
  Matrix.posSemidef_sum _ fun k _ => hX.mul_mul_conjTranspose_same (E k)

lemma kraus_trace {A B K : Type*} [Fintype A] [DecidableEq A] [Fintype B] [Fintype K]
    (E : K → Matrix B A ℂ) (hE : ∑ k, (E k)ᴴ * E k = 1) (X : Matrix A A ℂ) :
    trace (krausApply E X) = trace X := by
  show trace (∑ k, E k * X * (E k)ᴴ) = _
  rw [trace_sum]
  have : ∀ k, trace (E k * X * (E k)ᴴ) = trace ((E k)ᴴ * E k * X) := by
    intro k; rw [trace_mul_comm, ← Matrix.mul_assoc]
  simp only [this, ← trace_sum, ← Matrix.sum_mul, hE, Matrix.one_mul]

variable {R A B C K L : Type*} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L]

lemma stV_iso (F : L → Matrix C B ℂ) (hF : ∑ l, (F l)ᴴ * F l = 1) : (stV F)ᴴ * stV F = 1 := by
  rw [← hF]
  ext b b'
  simp only [stV, mul_apply, conjTranspose_apply, of_apply, Fintype.sum_prod_type, Matrix.sum_apply]
  exact Finset.sum_comm

lemma kraus_id (X : Matrix B B ℂ) : krausApply (fun _ : Unit => (1 : Matrix B B ℂ)) X = X := by
  simp [krausApply]

lemma idT_id (Y : Matrix (R × B) (R × B) ℂ) :
    idTensorSuperop (krausApply (fun _ : Unit => (1 : Matrix B B ℂ))) Y = Y := by
  ext p q; simp only [idTensorSuperop, kraus_id, of_apply]

/-- entropy of `id ⊗ E` on a pure state = entropy of the complementary output. -/
theorem sc [Nonempty R] [Nonempty B] [Nonempty K] (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) :
    vnEntropy (idTensorSuperop (krausApply E) (pureDensity (vecOf Ψ))) =
      vnEntropy (comp E (Ψ * Ψᴴ)) := by
  have h := m_RC Ψ E (fun _ : Unit => (1 : Matrix B B ℂ))
  rw [idT_id] at h
  rw [← h, pure_comp, ← m_K Ψ E (fun _ : Unit => (1 : Matrix B B ℂ)) (by simp)]
  refine vn_marg_eq sK _ ?_ ?_ (pd_psd _)
  all_goals intro ω ω'
  all_goals simp only [sK, sRC, Equiv.coe_fn_mk, Equiv.trans_apply, Equiv.prodComm_apply,
    Prod.swap_prod_mk, Prod.ext_iff]
  all_goals simp

section ineq
variable [Nonempty R] [Nonempty C] [Nonempty L] [Nonempty K]

def p1 : R × (C × (L × K)) ≃ (R × (L × K)) × C where
  toFun x := ((x.1, (x.2.2.1, x.2.2.2)), x.2.1)
  invFun y := (y.1.1, (y.2, (y.1.2.1, y.1.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

def p2 : R × (C × (L × K)) ≃ (C × (K × L)) × R where
  toFun x := ((x.2.1, (x.2.2.2, x.2.2.1)), x.1)
  invFun y := (y.2, (y.1.1, (y.1.2.2, y.1.2.1)))
  left_inv _ := rfl
  right_inv _ := rfl

lemma tr_one (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ)
    (hE : ∑ k, (E k)ᴴ * E k = 1) (hF : ∑ l, (F l)ᴴ * F l = 1) (hΨ : trace (Ψ * Ψᴴ) = 1) :
    trace (pureDensity (lam Ψ E F)) = 1 := by
  rw [← marg_trace (Equiv.refl _), m_R Ψ E F hE hF, trace_transpose, trace_mul_comm, hΨ]

/-- the four inequalities: with `σ = ΨΨᴴ`, `S(K)+S(C) ≤ S(CL)+S(RC)`, `S(R)+S(L) ≤ S(RC)+S(CL)`,
`S(CL) ≤ S(C)+S(L)`, `S(CL) ≤ S(R)+S(K)`. -/
theorem ineqs (Ψ : Matrix A R ℂ) (E : K → Matrix B A ℂ) (F : L → Matrix C B ℂ)
    (hE : ∑ k, (E k)ᴴ * E k = 1) (hF : ∑ l, (F l)ᴴ * F l = 1) (hΨ : trace (Ψ * Ψᴴ) = 1) :
    let SR := vnEntropy (Ψ * Ψᴴ)
    let SC := vnEntropy (krausApply F (krausApply E (Ψ * Ψᴴ)))
    let SRC := vnEntropy
      (idTensorSuperop (krausApply F) (idTensorSuperop (krausApply E) (pureDensity (vecOf Ψ))))
    let SK := vnEntropy (comp E (Ψ * Ψᴴ))
    let SL := vnEntropy (comp F (krausApply E (Ψ * Ψᴴ)))
    let SCL := vnEntropy (krausApply E (Ψ * Ψᴴ))
    SK + SC ≤ SCL + SRC ∧ SR + SL ≤ SRC + SCL ∧ SCL ≤ SC + SL ∧ SCL ≤ SR + SK := by
  intro SR SC SRC SK SL SCL
  have hP : (pureDensity (lam Ψ E F)).PosSemidef := pd_psd _
  have ht : trace (pureDensity (lam Ψ E F)) = 1 := tr_one Ψ E F hE hF hΨ
  have eR : vnEntropy (marg (Equiv.refl _) (pureDensity (lam Ψ E F))) = SR := by
    rw [m_R Ψ E F hE hF, vn_transpose (isHermitian_conjTranspose_mul_self Ψ), ← vn_mul_conj]
  have eC : vnEntropy (marg sC (pureDensity (lam Ψ E F))) = SC := by rw [m_C]
  have eRC : vnEntropy (marg sRC (pureDensity (lam Ψ E F))) = SRC := by rw [m_RC]
  have eK : vnEntropy (marg sK (pureDensity (lam Ψ E F))) = SK := by rw [m_K Ψ E F hF]
  have eL : vnEntropy (marg sL (pureDensity (lam Ψ E F))) = SL := by rw [m_L]
  have eCL : vnEntropy (marg sCL (pureDensity (lam Ψ E F))) = SCL := by
    rw [m_CL, vn_iso _ (stV_iso F hF) _ (kraus_psd E (posSemidef_self_mul_conjTranspose Ψ))]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := ssa_split p1 (pureDensity (lam Ψ E F)) hP ht
    rw [pure_comp (p1.trans r21), pure_comp (p1.trans r31), pure_comp p1] at h
    rw [vn_marg_eq sCL ((p1.trans r21).trans (Equiv.prodComm _ _)) ?_ ?_ hP,
      vn_marg_eq sRC ((p1.trans r31).trans (Equiv.prodComm _ _)) ?_ ?_ hP,
      vn_marg_eq sK (p1.trans r1) ?_ ?_ hP,
      vn_marg_eq sC (p1.trans (Equiv.prodComm _ _)) ?_ ?_ hP, eCL, eRC, eK, eC] at h
    · linarith
    all_goals intro ω ω'
    all_goals simp only [sK, sRC, sCL, sC, p1, r21, r31, r1, Equiv.coe_fn_mk, Equiv.trans_apply,
      Equiv.prodComm_apply, Prod.swap_prod_mk, Prod.ext_iff]
    all_goals tauto
  · have h := ssa_split p2 (pureDensity (lam Ψ E F)) hP ht
    rw [pure_comp (p2.trans r31), pure_comp p2] at h
    rw [vn_marg_eq sCL (p2.trans r21) ?_ ?_ hP,
      vn_marg_eq sRC ((p2.trans r31).trans (Equiv.prodComm _ _)) ?_ ?_ hP,
      vn_marg_eq sL (p2.trans r1) ?_ ?_ hP,
      vn_marg_eq (Equiv.refl _) (p2.trans (Equiv.prodComm _ _)) ?_ ?_ hP, eCL, eRC, eL, eR] at h
    · linarith
    all_goals intro ω ω'
    all_goals simp only [sL, sRC, sCL, p2, r21, r31, r1, Equiv.coe_fn_mk, Equiv.trans_apply,
      Equiv.prodComm_apply, Prod.swap_prod_mk, Prod.ext_iff, Equiv.refl_apply]
    all_goals tauto
  · have h := subadd_split sCL (pureDensity (lam Ψ E F)) hP ht
    rw [vn_marg_eq sC (sCL.trans rX) ?_ ?_ hP, vn_marg_eq sL (sCL.trans rY) ?_ ?_ hP,
      eCL, eC, eL] at h
    · exact h
    all_goals intro ω ω'
    all_goals simp only [sL, sC, sCL, rX, rY, Equiv.coe_fn_mk, Equiv.trans_apply,
      Equiv.prodAssoc_apply, Prod.ext_iff]
    all_goals tauto
  · have h := subadd_split (sCL.trans (Equiv.prodComm _ _)) (pureDensity (lam Ψ E F)) hP ht
    rw [← pure_comp, vn_marg_eq (Equiv.refl _) ((sCL.trans (Equiv.prodComm _ _)).trans rX) ?_ ?_ hP,
      vn_marg_eq sK ((sCL.trans (Equiv.prodComm _ _)).trans rY) ?_ ?_ hP,
      eCL, eR, eK] at h
    · exact h
    all_goals intro ω ω'
    all_goals simp only [sK, sCL, rX, rY, Equiv.coe_fn_mk, Equiv.trans_apply,
      Equiv.prodAssoc_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, Prod.ext_iff, Equiv.refl_apply]
    all_goals tauto

end ineq
end X6CH


/-! X6 channel library, part 4: bridge to `entropyExchange`/`inputMutualInfo`/`loss` and the
data-processing inequalities of Adami–Cerf. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CH
open Matrix X6SSA QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)

variable {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]

lemma sqrt_herm (ρ : Matrix A A ℂ) : (cfc Real.sqrt ρ)ᴴ = cfc Real.sqrt ρ := by
  have : IsSelfAdjoint (cfc Real.sqrt ρ) := cfc_predicate _ _
  exact this

lemma sqrt_sq {ρ : Matrix A A ℂ} (hρ : ρ.PosSemidef) :
    cfc Real.sqrt ρ * (cfc Real.sqrt ρ)ᴴ = ρ := by
  open scoped MatrixOrder in
  have h0 : (0 : Matrix A A ℂ) ≤ ρ := Matrix.nonneg_iff_posSemidef.mpr hρ
  rw [sqrt_herm, ← cfc_mul Real.sqrt Real.sqrt ρ]
  conv_rhs => rw [← cfc_id ℝ ρ]
  open scoped MatrixOrder in
  exact cfc_congr fun x hx => Real.mul_self_sqrt (spectrum_nonneg_of_nonneg h0 hx)

/-- the entropy exchange through the canonical purification. -/
lemma ee_eq (N : Superop A B) {ρ : Matrix A A ℂ} (hρ : ρ.IsHermitian) :
    entropyExchange N ρ =
      vnEntropy (idTensorSuperop N (pureDensity (vecOf (cfc Real.sqrt ρ)))) := by
  unfold entropyExchange
  simp only []
  congr 3
  ext z
  simp only [canonicalPurification, vecOf, PiLp.toLp_apply]
  have h := map_cfc_mat (reind (Fintype.equivFin A)) Real.sqrt ρ hρ
  simp only [reind_apply] at h
  have e : (fun i j => ρ ((Fintype.equivFin A).symm i) ((Fintype.equivFin A).symm j)) =
      reindex (Fintype.equivFin A) (Fintype.equivFin A) ρ := rfl
  rw [e, ← h]
  simp

lemma kraus_of_channel [Nonempty A] {N : Superop A B} (hN : IsChannel N) :
    ∃ (m : ℕ) (E : Fin m → Matrix B A ℂ), 0 < m ∧ ∑ k, (E k)ᴴ * E k = 1 ∧ N = krausApply E := by
  obtain ⟨m, E, hE, hNE⟩ := hN
  refine ⟨m, E, ?_, hE, funext hNE⟩
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    obtain ⟨a⟩ := ‹Nonempty A›
    have := congrFun (congrFun hE a) a
    simp at this
  · exact h

lemma idT_comp {R : Type*} (M : Superop B C) (N : Superop A B) (X : Matrix (R × A) (R × A) ℂ) :
    idTensorSuperop (M ∘ N) X = idTensorSuperop M (idTensorSuperop N X) := rfl

/-- all entropic quantities of the two-channel problem, in terms of the Stinespring state. -/
theorem dpi [Nonempty A] [Nonempty B] [Nonempty C]
    (N : Superop A B) (M : Superop B C) (hN : IsChannel N) (hM : IsChannel M)
    (ρ : Matrix A A ℂ) (hρ : IsDensityMatrix ρ) :
    inputMutualInfo (M ∘ N) ρ ≤ inputMutualInfo N ρ ∧
    inputMutualInfo N ρ ≤ 2 * vnEntropy ρ ∧
    inputMutualInfo (M ∘ N) ρ ≤ inputMutualInfo M (N ρ) ∧
    inputMutualInfo M (N ρ) ≤ 2 * vnEntropy (M (N ρ)) ∧
    0 ≤ vnEntropy ρ + entropyExchange N ρ - vnEntropy (N ρ) ∧
    vnEntropy ρ + entropyExchange N ρ - vnEntropy (N ρ) ≤
      vnEntropy ρ + entropyExchange (M ∘ N) ρ - vnEntropy (M (N ρ)) := by
  obtain ⟨m, E, hm, hE, rfl⟩ := kraus_of_channel hN
  obtain ⟨m', F, hm', hF, rfl⟩ := kraus_of_channel hM
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Nonempty (Fin m') := ⟨⟨0, hm'⟩⟩
  set s := cfc Real.sqrt ρ
  have hs : s * sᴴ = ρ := sqrt_sq hρ.1
  have hΨ : trace (s * sᴴ) = 1 := by rw [hs, hρ.2]
  have hNρ : (krausApply E ρ).PosSemidef := kraus_psd E hρ.1
  set t := cfc Real.sqrt (krausApply E ρ)
  have ht : t * tᴴ = krausApply E ρ := sqrt_sq hNρ
  obtain ⟨i1, i2, i3, i4⟩ := ineqs s E F hE hF hΨ
  simp only [hs] at i1 i2 i3 i4
  have eN : entropyExchange (krausApply E) ρ = vnEntropy (comp E ρ) := by
    rw [ee_eq _ hρ.1.isHermitian, sc, hs]
  have eM : entropyExchange (krausApply F) (krausApply E ρ) =
      vnEntropy (comp F (krausApply E ρ)) := by
    rw [ee_eq _ hNρ.isHermitian, sc, ht]
  have eMN : entropyExchange (krausApply F ∘ krausApply E) ρ =
      vnEntropy (idTensorSuperop (krausApply F)
        (idTensorSuperop (krausApply E) (pureDensity (vecOf s)))) := by
    rw [ee_eq _ hρ.1.isHermitian, idT_comp]
  unfold inputMutualInfo
  simp only [Function.comp_apply, eN, eM, eMN]
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- `I(R:A)` of the canonical purification of a density matrix is `2 S(τ)`. -/
lemma mi_pure {A : Type} [Fintype A] [DecidableEq A] [Nonempty A] {τ : Matrix A A ℂ} (hτ : IsDensityMatrix τ) :
    QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation
      (pureDensity (canonicalPurification τ)) = 2 * vnEntropy τ := by
  unfold QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation
  set u := cfc Real.sqrt τ
  have hu : u * uᴴ = τ := sqrt_sq hτ.1
  have hv : canonicalPurification τ = vecOf u := rfl
  have hL : traceLeft (pureDensity (vecOf u)) = u * uᴴ := by
    ext a a'
    simp [traceLeft, pureDensity, vecOf, mul_apply, conjTranspose_apply]
  have hRL : vnEntropy (traceRight (pureDensity (vecOf u))) =
      vnEntropy (traceLeft (pureDensity (vecOf u))) := vn_pure_marginals (vecOf u)
  let Mv : Matrix (A × A) Unit ℂ := of fun p _ => vecOf u p
  have h1 : pureDensity (vecOf u) = Mv * Mvᴴ := by
    ext p q; simp [pureDensity, Mv, mul_apply, conjTranspose_apply]
  have h2 : Mvᴴ * Mv = 1 := by
    ext i j
    have : (Mvᴴ * Mv) i j = trace (u * uᴴ) := by
      simp only [Mv, mul_apply, conjTranspose_apply, of_apply, trace, diag_apply, vecOf,
        PiLp.toLp_apply, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun r _ => ?_
      simp [mul_comm]
    rw [this, hu, hτ.2]; simp [one_apply]
  rw [hv, hRL, hL, hu, h1, vn_mul_conj, h2, vn_one]
  ring

end X6CH


/-! X6 channel library, part 5: the loss/information balance for a single Kraus channel, via the
Stinespring state `lam Ψ E 1`. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CH
open Matrix X6SSA QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)
open QAlgorithms.Papers.Independent.Dependency50.P45 (entropyExchange inputMutualInfo)
open QAlgorithms.Papers.Independent.Gap48.P33

variable {A B K : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype K] [DecidableEq K]

/-- the identity Kraus family. -/
def F0 : Unit → Matrix B B ℂ := fun _ => 1

lemma kraus_F0 (X : Matrix B B ℂ) : krausApply (F0 (B := B)) X = X := kraus_id X

lemma idT_F0 {R : Type*} [Fintype R] [DecidableEq R] (Y : Matrix (R × B) (R × B) ℂ) :
    idTensorSuperop (krausApply (F0 (B := B))) Y = Y := idT_id Y

lemma F0_kraus : ∑ l, (F0 (B := B) l)ᴴ * F0 l = 1 := by simp [F0]

lemma vn_pd_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι)
    (h : trace (pureDensity v) = 1) : vnEntropy (pureDensity v) = 0 := by
  let Mv : Matrix ι Unit ℂ := of fun p _ => v p
  have h1 : pureDensity v = Mv * Mvᴴ := by
    ext p q; simp [pureDensity, Mv, mul_apply, conjTranspose_apply]
  have h2 : Mvᴴ * Mv = 1 := by
    ext i j
    have : (Mvᴴ * Mv) i j = trace (pureDensity v) := by
      simp only [Mv, mul_apply, conjTranspose_apply, of_apply, trace, diag_apply, pureDensity]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp [mul_comm]
    rw [this, h]; simp [one_apply]
  rw [h1, vn_mul_conj, h2, vn_one]

lemma comp_F0 (σ : Matrix B B ℂ) (hσ : trace σ = 1) : vnEntropy (comp (F0 (B := B)) σ) = 0 := by
  have : comp (F0 (B := B)) σ = 1 := by
    ext i j; simp [comp, F0, hσ, one_apply]
  rw [this, vn_one]

def sKB : A × (B × (Unit × K)) ≃ (K × B) × (A × Unit) where
  toFun x := ((x.2.2.2, x.2.1), (x.1, x.2.2.1))
  invFun y := (y.2.1, (y.1.2, (y.2.2, y.1.1)))
  left_inv _ := rfl
  right_inv _ := rfl

def sRK : A × (B × (Unit × K)) ≃ (A × K) × (B × Unit) where
  toFun x := ((x.1, x.2.2.2), (x.2.1, x.2.2.1))
  invFun y := (y.1.1, (y.2.1, (y.2.2, y.1.2)))
  left_inv _ := rfl
  right_inv _ := rfl

theorem balance [Nonempty A] [Nonempty B] [Nonempty K]
    (E : K → Matrix B A ℂ) (hE : IsKrausFamily E)
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho) :
    let N := krausApply E
    let omega := pureDensity (dilationReference E (canonicalPurification rho))
    loss N rho = middleConditionalInformation omega ∧
    loss N rho = QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation
      (discardMiddle omega) ∧
    entropyExchange N rho = vnEntropy (traceLeft (traceLeft omega)) ∧
    0 ≤ loss N rho ∧ loss N rho ≤ 2 * min (vnEntropy rho) (entropyExchange N rho) ∧
    inputMutualInfo N rho + loss N rho = 2 * vnEntropy rho ∧
    0 ≤ inputMutualInfo N rho ∧ inputMutualInfo N rho ≤ 2 * vnEntropy rho := by
  intro N omega
  have hE' : ∑ k, (E k)ᴴ * E k = 1 := hE
  set s := cfc Real.sqrt rho
  have hs : s * sᴴ = rho := sqrt_sq hrho.1
  have hΨ : trace (s * sᴴ) = 1 := by rw [hs, hrho.2]
  have hNρ : (krausApply E rho).PosSemidef := kraus_psd E hrho.1
  have htN : trace (krausApply E rho) = 1 := by rw [kraus_trace E hE', hrho.2]
  set P := pureDensity (lam s E (F0 (B := B)))
  have hP : P.PosSemidef := pd_psd _
  have hPt : trace P = 1 := tr_one s E F0 hE' F0_kraus hΨ
  -- entries of omega
  have hω : ∀ x y : A × (B × K), omega x y =
      P (x.1, (x.2.1, ((), x.2.2))) (y.1, (y.2.1, ((), y.2.2))) := by
    intro x y
    simp [omega, P, pureDensity, dilationReference, lam, F0, canonicalPurification, s, mul_apply]
  -- entropies of the Stinespring state
  obtain ⟨i1, i2, i3, i4⟩ := ineqs s E (F0 (B := B)) hE' F0_kraus hΨ
  simp only [hs, kraus_F0, idT_F0, comp_F0 _ htN] at i1 i2 i3 i4
  rw [← ee_eq _ hrho.1.isHermitian] at i1 i2
  have eEE : entropyExchange N rho = vnEntropy (comp E rho) := by
    rw [ee_eq _ hrho.1.isHermitian, sc, hs]
  have eR : vnEntropy (marg (Equiv.refl _) P) = vnEntropy rho := by
    rw [m_R s E F0 hE' F0_kraus, vn_transpose (isHermitian_conjTranspose_mul_self s), ← vn_mul_conj,
      hs]
  have eC : vnEntropy (marg sC P) = vnEntropy (N rho) := by
    rw [m_C, kraus_F0, hs]
  have eRC : vnEntropy (marg sRC P) = entropyExchange N rho := by
    rw [m_RC, idT_F0, ee_eq _ hrho.1.isHermitian]
  have eK : vnEntropy (marg sK P) = entropyExchange N rho := by
    rw [m_K s E F0 F0_kraus, hs, eEE]
  have eCL : vnEntropy (marg sCL P) = vnEntropy (N rho) := by
    rw [m_CL, vn_iso _ (stV_iso F0 F0_kraus) _ (kraus_psd E (posSemidef_self_mul_conjTranspose s)), hs]
  have eKB : vnEntropy (marg sKB P) = vnEntropy rho := by
    rw [pure_comp, ← eR]
    refine vn_marg_eq (Equiv.refl _) _ ?_ ?_ hP
    all_goals intro ω ω'
    all_goals simp only [sKB, Equiv.coe_fn_mk, Equiv.trans_apply, Equiv.prodComm_apply,
      Prod.swap_prod_mk, Prod.ext_iff, Equiv.refl_apply]
    all_goals (try simp)
    all_goals (try tauto)
  have eRK : vnEntropy (marg sRK P) = vnEntropy (N rho) := by
    rw [pure_comp, ← eCL]
    refine vn_marg_eq sCL _ ?_ ?_ hP
    all_goals intro ω ω'
    all_goals simp only [sRK, sCL, Equiv.coe_fn_mk, Equiv.trans_apply, Equiv.prodComm_apply,
      Prod.swap_prod_mk, Prod.ext_iff]
    all_goals (try simp)
    all_goals (try tauto)
  have sub : vnEntropy (marg sRC P) ≤ vnEntropy (marg (Equiv.refl _) P) + vnEntropy (marg sC P) := by
    have h := subadd_split sRC P hP hPt
    rw [vn_marg_eq (Equiv.refl _) (sRC.trans rX) ?_ ?_ hP, vn_marg_eq sC (sRC.trans rY) ?_ ?_ hP] at h
    · exact h
    all_goals intro ω ω'
    all_goals simp only [sRC, sC, rX, rY, Equiv.coe_fn_mk, Equiv.trans_apply,
      Equiv.prodAssoc_apply, Prod.ext_iff, Equiv.refl_apply]
    all_goals tauto
  -- the matrices of the statement as marginals
  have hM0 : vnEntropy omega = 0 := vn_pd_zero _ (by
    show trace omega = 1
    rw [← hPt]
    simp only [trace, diag_apply, hω, Fintype.sum_prod_type, Finset.univ_unique, Finset.sum_singleton]
    try rfl)
  have hMCI : middleConditionalInformation omega = vnEntropy (marg sRC P) +
      vnEntropy (marg sKB P) - vnEntropy (marg sC P) := by
    show vnEntropy (fun i j : A × B => ∑ b : K, omega (i.1, (i.2, b)) (j.1, (j.2, b))) +
      vnEntropy (fun i j : K × B => ∑ a : A, omega (a, (i.2, i.1)) (a, (j.2, j.1))) -
      vnEntropy (traceLeft (fun x y : (A × K) × B => omega (x.1.1, (x.2, x.1.2)) (y.1.1, (y.2, y.1.2)))) -
      vnEntropy (fun x y : (A × K) × B => omega (x.1.1, (x.2, x.1.2)) (y.1.1, (y.2, y.1.2))) = _
    have e4 : vnEntropy (fun x y : (A × K) × B => omega (x.1.1, (x.2, x.1.2)) (y.1.1, (y.2, y.1.2))) =
        vnEntropy omega := by
      have := vn_reind (show A × (B × K) ≃ (A × K) × B from
        { toFun := fun x => ((x.1, x.2.2), x.2.1), invFun := fun y => (y.1.1, (y.2, y.1.2)),
          left_inv := fun _ => rfl, right_inv := fun _ => rfl }) omega (pd_psd _).1
      exact this
    have h1 : (fun i j : A × B => ∑ b : K, omega (i.1, (i.2, b)) (j.1, (j.2, b))) = marg sRC P := by
      ext i j
      simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, sRC, Equiv.coe_fn_symm_mk,
        Fintype.sum_prod_type, hω]
      simp
    have h2 : (fun i j : K × B => ∑ a : A, omega (a, (i.2, i.1)) (a, (j.2, j.1))) = marg sKB P := by
      ext i j
      simp only [marg, trR, reindex_apply, submatrix_apply, of_apply, sKB, Equiv.coe_fn_symm_mk,
        Fintype.sum_prod_type, hω]
      simp
    have h3 : traceLeft (fun x y : (A × K) × B => omega (x.1.1, (x.2, x.1.2)) (y.1.1, (y.2, y.1.2))) =
        marg sC P := by
      ext i j
      simp only [traceLeft, marg, trR, reindex_apply, submatrix_apply, of_apply, sC,
        Equiv.coe_fn_symm_mk, Fintype.sum_prod_type, hω]
      simp
    rw [e4, hM0, h1, h2, h3]; ring
  have hD : discardMiddle omega = marg sRK P := by
    ext i j
    simp only [discardMiddle, marg, trR, reindex_apply, submatrix_apply, of_apply, sRK,
      Equiv.coe_fn_symm_mk, Fintype.sum_prod_type, hω]
    simp
  have hDR : traceRight (marg sRK P) = marg (Equiv.refl _) P := by
    ext i j
    simp only [traceRight, marg, trR, reindex_apply, submatrix_apply, of_apply, sRK,
      Equiv.coe_fn_symm_mk, Fintype.sum_prod_type, Equiv.refl_symm, Equiv.refl_apply]
    try simp only [Finset.univ_unique, Finset.sum_singleton]
    try exact Finset.sum_comm
  have hDL : traceLeft (marg sRK P) = marg sK P := by
    ext i j
    simp only [traceLeft, marg, trR, reindex_apply, submatrix_apply, of_apply, sRK, sK,
      Equiv.coe_fn_symm_mk, Fintype.sum_prod_type]
    try simp only [Finset.univ_unique, Finset.sum_singleton]
    try rfl
  have hLL : traceLeft (traceLeft omega) = marg sK P := by
    ext i j
    simp only [traceLeft, marg, trR, reindex_apply, submatrix_apply, of_apply, sK,
      Equiv.coe_fn_symm_mk, Fintype.sum_prod_type, hω]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    exact Finset.sum_comm
  have hL : loss N rho = vnEntropy rho + entropyExchange N rho - vnEntropy (N rho) := rfl
  have hI : inputMutualInfo N rho = vnEntropy rho + vnEntropy (N rho) - entropyExchange N rho := rfl
  rw [eR, eC, eRC] at sub
  rw [← eEE] at i4
  have hmin : 2 * min (vnEntropy rho) (entropyExchange N rho) =
      min (2 * vnEntropy rho) (2 * entropyExchange N rho) :=
    mul_min_of_nonneg _ _ (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hMCI, eRC, eKB, eC, hL]; ring
  · unfold QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation
    rw [hD, hDR, hDL, eR, eK, eRK, hL]
  · rw [hLL, eK]
  · rw [hL]; linarith
  · rw [hmin, hL]; exact le_min (by linarith) (by linarith)
  · rw [hL, hI]; ring
  · rw [hI]; linarith
  · rw [hI]; linarith

end X6CH


noncomputable section

open Polynomial

namespace X6G41D

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma spec_sub (d : n → ℝ) : spectrum ℝ (Matrix.diagonal (fun i => (d i : ℂ))) ⊆ Set.range d := by
  intro μ hμ
  by_contra hc
  rw [spectrum.mem_iff] at hμ
  apply hμ
  have e : (μ • 1 : Matrix n n ℂ) = Matrix.diagonal (fun _ => (μ : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Complex.real_smul]
    · simp [Matrix.one_apply, h]
  rw [Algebra.algebraMap_eq_smul_one, e, Matrix.diagonal_sub,
    Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro i
  simp only [isUnit_iff_ne_zero, ne_eq, sub_eq_zero]
  intro h
  apply hc
  refine ⟨i, ?_⟩
  have := congrArg Complex.re h
  simpa using this.symm

lemma aeval_diag (d : n → ℝ) (P : ℝ[X]) :
    aeval (Matrix.diagonal (fun i => (d i : ℂ))) P =
      Matrix.diagonal (fun i => ((P.eval (d i) : ℝ) : ℂ)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, Matrix.diagonal_add]
  | monomial k a =>
    rw [aeval_monomial, Matrix.diagonal_pow, Algebra.algebraMap_eq_smul_one, smul_one_mul,
      ← Matrix.diagonal_smul]
    congr 1; funext i
    simp only [eval_monomial, Pi.smul_apply, Pi.pow_apply, Complex.real_smul]
    push_cast; ring

lemma cfc_diag (d : n → ℝ) (f : ℝ → ℝ) :
    cfc f (Matrix.diagonal (fun i => (d i : ℂ))) = Matrix.diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  classical
  set S := Finset.univ.image d
  set P := Lagrange.interpolate S id f
  have hP : ∀ i, P.eval (d i) = f (d i) := by
    intro i
    have := Lagrange.eval_interpolate_at_node (s := S) (v := id) (r := f)
      (Set.injOn_id _) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    rwa [id] at this
  have hsa : IsSelfAdjoint (Matrix.diagonal (fun i => (d i : ℂ))) := by
    rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1; funext i; simp
  rw [cfc_congr (g := fun t => P.eval t), cfc_polynomial P _ hsa, aeval_diag]
  · congr 1; funext i; rw [hP]
  · intro t ht
    obtain ⟨i, rfl⟩ := spec_sub d ht
    exact (hP i).symm

end X6G41D


/-! X6 channel library, part 6: entropy of block-diagonal (classical-quantum) states, concavity of
the conditional entropy `S(XY) - S(Y)` and of the entropy, from strong subadditivity. -/

open scoped Matrix.Norms.L2Operator ComplexOrder Kronecker Matrix ComplexConjugate
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6CH
open Matrix X6SSA QAlgorithms Real

lemma vn_diag' {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ) :
    vnEntropy (Matrix.diagonal fun i => (f i : ℂ)) = ∑ i, negMulLog (f i) / log 2 := by
  unfold vnEntropy
  rw [X6G41D.cfc_diag, Matrix.trace_diagonal, Complex.re_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.ofReal_re, Real.logb, negMulLog]
  ring

lemma vn_eig' {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    vnEntropy A = ∑ i, negMulLog (hA.eigenvalues i) / log 2 := by
  rw [vn_eig hA]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Real.logb, negMulLog]
  ring

lemma eig_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (htr : trace A = 1) : ∑ i, hA.eigenvalues i = 1 := by
  have h := hA.trace_eq_sum_eigenvalues
  rw [htr] at h
  have h2 : ((∑ i, hA.eigenvalues i : ℝ) : ℂ) = 1 := by rw [h]; push_cast; rfl
  exact_mod_cast h2

section blocks
variable {Z J : Type*} [Fintype Z] [DecidableEq Z] [Fintype J] [DecidableEq J]

/-- entropy of a block-diagonal mixture `⊕_j w_j ω_j`, in bits. -/
theorem blk_ent (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (ω : J → Matrix Z Z ℂ)
    (hω : ∀ j, (ω j).PosSemidef) (htr : ∀ j, trace (ω j) = 1) :
    vnEntropy (blockDiagonal fun j => (w j : ℂ) • ω j) =
      ∑ j, negMulLog (w j) / log 2 + ∑ j, w j * vnEntropy (ω j) := by
  let U : J → Matrix Z Z ℂ := fun j => ((hω j).1.eigenvectorUnitary : Matrix Z Z ℂ)
  let lam : J → Z → ℝ := fun j => (hω j).1.eigenvalues
  have hU : ∀ j, (U j)ᴴ * U j = 1 := fun j =>
    Unitary.star_mul_self_of_mem (hω j).1.eigenvectorUnitary.2
  have hdec : ∀ j, (w j : ℂ) • ω j =
      U j * diagonal (fun i => ((w j * lam j i : ℝ) : ℂ)) * (U j)ᴴ := by
    intro j
    have h := (hω j).1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    conv_lhs => rw [h]
    have : diagonal (fun i => ((w j * lam j i : ℝ) : ℂ)) =
        (w j : ℂ) • diagonal (RCLike.ofReal ∘ (hω j).1.eigenvalues) := by
      ext a b; by_cases hab : a = b <;> simp [diagonal_apply, hab, lam]
    rw [this, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  have hB : (blockDiagonal fun j => (w j : ℂ) • ω j) =
      blockDiagonal U * diagonal (fun p : Z × J => ((w p.2 * lam p.2 p.1 : ℝ) : ℂ)) *
        (blockDiagonal U)ᴴ := by
    simp only [hdec]
    rw [blockDiagonal_mul, blockDiagonal_mul, blockDiagonal_conjTranspose, blockDiagonal_diagonal]
  have hW : (blockDiagonal U)ᴴ * blockDiagonal U = 1 := by
    rw [blockDiagonal_conjTranspose, ← blockDiagonal_mul]
    simp only [hU]
    exact blockDiagonal_one
  have hD : (diagonal (fun p : Z × J => ((w p.2 * lam p.2 p.1 : ℝ) : ℂ))).PosSemidef := by
    refine Matrix.posSemidef_diagonal_iff.mpr fun p => ?_
    have := (hω p.2).eigenvalues_nonneg p.1
    exact_mod_cast mul_nonneg (hw p.2) this
  rw [hB, vn_iso _ hW _ hD, vn_diag']
  have key : ∀ j, ∑ i, negMulLog (w j * lam j i) / log 2 =
      negMulLog (w j) / log 2 + w j * vnEntropy (ω j) := by
    intro j
    simp only [negMulLog_mul, add_div, Finset.sum_add_distrib]
    rw [vn_eig' (hω j).1, Finset.mul_sum]
    congr 1
    · rw [← Finset.sum_div, ← Finset.sum_mul, eig_sum (hω j).1 (htr j), one_mul]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [lam]; ring
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [key, Finset.sum_add_distrib]

end blocks

section concave
variable {X Y J : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype J] [DecidableEq J]

lemma psd_smul {n : Type*} [Fintype n] {M : Matrix n n ℂ} (hM : M.PosSemidef) {c : ℝ}
    (hc : 0 ≤ c) : ((c : ℂ) • M).PosSemidef := by
  have := hM.smul (show (0 : ℂ) ≤ (c : ℂ) from by exact_mod_cast hc)
  exact this

lemma blk_psd {Z : Type*} [Fintype Z] [DecidableEq Z] (M : J → Matrix Z Z ℂ)
    (hM : ∀ j, (M j).PosSemidef) : (blockDiagonal M).PosSemidef := by
  let P : J → Matrix Z (Z × J) ℂ := fun j => of fun z p => if p = (z, j) then 1 else 0
  have : blockDiagonal M = ∑ j, (P j)ᴴ * M j * P j := by
    ext p q
    simp only [blockDiagonal_apply, Matrix.sum_apply, mul_apply, conjTranspose_apply, P, of_apply]
    simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
      mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Prod.ext_iff]
    obtain ⟨z, j⟩ := p
    obtain ⟨z', j'⟩ := q
    simp only
    by_cases h : j = j'
    · subst h
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    · rw [if_neg h]
      refine (Finset.sum_eq_zero fun b _ => ?_).symm
      by_cases h1 : j = b
      · subst h1; simp [h, Ne.symm h]
      · simp [h1]
  rw [this]
  exact Matrix.posSemidef_sum _ fun j _ => (hM j).conjTranspose_mul_mul_same (P j)

/-- concavity of the conditional entropy `S(XY) - S(Y)` (from SSA). -/
theorem cond_concave [Nonempty X] [Nonempty Y] (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (ω : J → Matrix (X × Y) (X × Y) ℂ) (hω : ∀ j, IsDensityMatrix (ω j)) :
    ∑ j, w j * (vnEntropy (ω j) - vnEntropy (trF (ω j))) ≤
      vnEntropy (∑ j, (w j : ℂ) • ω j) - vnEntropy (trF (∑ j, (w j : ℂ) • ω j)) := by
  haveI : Nonempty J := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hw1
  let e : (X × Y) × J ≃ X × (J × Y) :=
    { toFun := fun p => (p.1.1, (p.2, p.1.2)), invFun := fun q => ((q.1, q.2.2), q.2.1),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  let e' : Y × J ≃ J × Y := Equiv.prodComm Y J
  set Bl := blockDiagonal fun j => (w j : ℂ) • ω j
  set τ := reindex e e Bl
  have hBl : Bl.PosSemidef := blk_psd _ fun j => psd_smul (hω j).1 (hw j)
  have hτ : τ.PosSemidef := by simp only [τ, reindex_apply]; exact hBl.submatrix _
  have hτt : trace τ = 1 := by
    simp only [τ]
    rw [trace_reind, trace_blockDiagonal]
    simp only [trace_smul, (hω _).2, smul_eq_mul, mul_one]
    exact_mod_cast hw1
  have h := ssa τ hτ hτt
  have e1 : trB τ = ∑ j, (w j : ℂ) • ω j := by
    ext p q
    simp only [trB, τ, reindex_apply, submatrix_apply, of_apply, Bl, blockDiagonal_apply, e,
      Equiv.coe_fn_symm_mk, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    simp
  have e2 : trF τ = reindex e' e' (blockDiagonal fun j => (w j : ℂ) • trF (ω j)) := by
    ext p q
    simp only [trF, τ, reindex_apply, submatrix_apply, of_apply, Bl, blockDiagonal_apply, e, e',
      Equiv.coe_fn_symm_mk, Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
      Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp [Finset.mul_sum]
  have e3 : trF (trF τ) = trF (∑ j, (w j : ℂ) • ω j) := by
    rw [← e1, trF_trB]
  have hT : vnEntropy τ = ∑ j, negMulLog (w j) / log 2 + ∑ j, w j * vnEntropy (ω j) := by
    simp only [τ]
    rw [vn_reind _ _ hBl.1, blk_ent w hw ω (fun j => (hω j).1) fun j => (hω j).2]
  have hT2 : vnEntropy (trF τ) =
      ∑ j, negMulLog (w j) / log 2 + ∑ j, w j * vnEntropy (trF (ω j)) := by
    rw [e2, vn_reind _ _ (blk_psd _ fun j => psd_smul (trF_psd (hω j).1) (hw j)).1,
      blk_ent w hw _ (fun j => trF_psd (hω j).1) fun j => by rw [trace_trF, (hω j).2]]
  rw [e1, e3, hT, hT2] at h
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

/-- concavity of the entropy. -/
theorem ent_concave {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (σ : J → Matrix Z Z ℂ)
    (hσ : ∀ j, IsDensityMatrix (σ j)) :
    ∑ j, w j * vnEntropy (σ j) ≤ vnEntropy (∑ j, (w j : ℂ) • σ j) := by
  let e : Z ≃ Z × Unit := addU1
  have h := cond_concave (X := Z) (Y := Unit) w hw hw1 (fun j => reindex e e (σ j)) fun j =>
    ⟨by rw [reindex_apply]; exact (hσ j).1.submatrix _, by rw [trace_reind, (hσ j).2]⟩
  have t1 : ∀ M : Matrix Z Z ℂ, trace M = 1 → trF (reindex e e M) = 1 := by
    intro M hM
    ext i j
    have : trF (reindex e e M) i j = trace M := by
      simp [trF, e, addU1, trace, reindex_apply]
    rw [this, hM]; simp
  have hsum : ∑ j, (w j : ℂ) • reindex e e (σ j) = reindex e e (∑ j, (w j : ℂ) • σ j) := by
    ext a b; simp [reindex_apply, Matrix.sum_apply]
  have htr : trace (∑ j, (w j : ℂ) • σ j) = 1 := by
    rw [trace_sum]; simp only [trace_smul, (hσ _).2, smul_eq_mul, mul_one]; exact_mod_cast hw1
  have hH : (∑ j, (w j : ℂ) • σ j).IsHermitian :=
    (Matrix.posSemidef_sum _ fun j _ => psd_smul (hσ j).1 (hw j)).1
  rw [hsum, t1 _ htr, vn_one, vn_reind _ _ hH] at h
  have r1 : ∀ j, vnEntropy (reindex e e (σ j)) = vnEntropy (σ j) := fun j => vn_reind _ _ (hσ j).1.1
  have r2 : ∀ j, vnEntropy (trF (reindex e e (σ j))) = 0 := fun j => by rw [t1 _ (hσ j).2, vn_one]
  simp only [r1, r2, sub_zero] at h
  exact h

end concave
end X6CH


/-! Claimed50.P24: public-total direction (pure refinement and concavity). -/

open scoped Matrix ComplexConjugate ComplexOrder
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace X6P24
open Matrix QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P24
open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

attribute [local instance] Classical.propDecidable Classical.decEq

lemma spec_sum' {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hh : H.IsHermitian) :
    H = ∑ x, ((hh.eigenvalues x : ℝ) : ℂ) • pureDensity (hh.eigenvectorBasis x) := by
  have e : H = (hh.eigenvectorUnitary : Matrix ι ι ℂ) *
      diagonal (fun i => ((hh.eigenvalues i : ℝ) : ℂ)) * (hh.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
    conv_lhs => rw [hh.spectral_theorem]
    rfl
  conv_lhs => rw [e]
  ext a b
  simp only [mul_apply, diagonal_apply, conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
    pureDensity, of_apply, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.sum_mul, IsHermitian.eigenvectorUnitary_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

lemma pd_dens {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) :
    pureDensity ψ ∈ X6AT.Dens ι := by
  have h : pureDensity ψ = vecMulVec (fun a => ψ a) (star fun a => ψ a) := by
    ext a b; simp [pureDensity, vecMulVec_apply]
  constructor
  · rw [h]; exact Matrix.posSemidef_vecMulVec_self_star _
  · have h2 : ‖ψ‖ ^ 2 = 1 := by rw [hψ]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at h2
    simp only [Matrix.trace, Matrix.diag, pureDensity, of_apply]
    have : ∀ a, ψ a * conj (ψ a) = ((‖ψ a‖ ^ 2 : ℝ) : ℂ) := fun a => by
      rw [Complex.mul_conj']; norm_cast
    simp only [this]
    exact_mod_cast h2

lemma eig_sum' {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (htr : trace A = 1) : ∑ i, hA.eigenvalues i = 1 := by
  have h := hA.trace_eq_sum_eigenvalues
  rw [htr] at h
  have h2 : ((∑ i, hA.eigenvalues i : ℝ) : ℂ) = 1 := by rw [h]; push_cast; rfl
  exact_mod_cast h2

variable {I B E : Type} [Fintype I] [Fintype B] [Fintype E]
  [DecidableEq I] [DecidableEq B] [DecidableEq E] [Nonempty I] [Nonempty B] [Nonempty E]

lemma recv_lin (V : Dilation I B E) {J : Type} [Fintype J] (c : J → ℂ) (M : J → Matrix I I ℂ) :
    receiverChannel V (∑ j, c j • M j) = ∑ j, c j • receiverChannel V (M j) := by
  ext a b
  simp [receiverChannel, QAlgorithms.traceRight, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]

lemma comp_lin (V : Dilation I B E) {J : Type} [Fintype J] (c : J → ℂ) (M : J → Matrix I I ℂ) :
    complementaryChannel V (∑ j, c j • M j) = ∑ j, c j • complementaryChannel V (M j) := by
  ext a b
  simp [complementaryChannel, QAlgorithms.traceLeft, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- `att` for an arbitrary finite index type. -/
lemma attG (g h : Matrix I I ℂ → ℝ) {q : Fin (X6AT.KK I) → ℝ} {σ : Fin (X6AT.KK I) → Matrix I I ℂ}
    (hmax : ∀ (k : ℕ) (p : Fin k → ℝ) (ρ : Fin k → Matrix I I ℂ), (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
        (∀ i, ρ i ∈ X6AT.Dens I) →
        g (∑ i, p i • ρ i) - ∑ i, p i * h (ρ i) ≤ g (∑ i, q i • σ i) - ∑ i, q i * h (σ i))
    {T : Type} [Fintype T] (p : T → ℝ) (ρ : T → Matrix I I ℂ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (hρ : ∀ i, ρ i ∈ X6AT.Dens I) :
    g (∑ i, p i • ρ i) - ∑ i, p i * h (ρ i) ≤ g (∑ i, q i • σ i) - ∑ i, q i * h (σ i) := by
  let e := (Fintype.equivFin T).symm
  have := hmax (Fintype.card T) (fun k => p (e k)) (fun k => ρ (e k)) (fun k => hp _)
    (by rw [Equiv.sum_comp e p]; exact hp1) (fun k => hρ _)
  rwa [Equiv.sum_comp e (fun i => p i • ρ i), Equiv.sum_comp e (fun i => p i * h (ρ i))] at this

lemma conc {K : Type} [Fintype K] [DecidableEq K] [Nonempty K] {T : Type} [Fintype T]
    (Φ : Matrix I I ℂ → Matrix K K ℂ) (w : T → ℝ) (σ : T → Matrix I I ℂ) (hw : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (hd : ∀ j, Φ (σ j) ∈ X6AT.Dens K)
    (hlin : Φ (∑ j, (w j : ℂ) • σ j) = ∑ j, (w j : ℂ) • Φ (σ j)) :
    ∑ j, w j * vnEntropy (Φ (σ j)) ≤ vnEntropy (Φ (∑ j, (w j : ℂ) • σ j)) := by
  rw [hlin]
  have := X6CH.ent_concave w hw hw1 (fun j => Φ (σ j)) hd
  convert this using 2

lemma refine_ent (V : Dilation I B E) (hV : IsIsometry V) {ρ : Matrix I I ℂ} (hρ : ρ ∈ X6AT.Dens I) :
    ∑ i, hρ.1.1.eigenvalues i * vnEntropy (receiverChannel V (pureDensity (hρ.1.1.eigenvectorBasis i)))
      ≤ vnEntropy (receiverChannel V ρ) := by
  have hs := spec_sum' hρ.1.1
  conv_rhs => rw [hs]
  exact conc (receiverChannel V) _ _ (fun i => hρ.1.eigenvalues_nonneg i) (eig_sum' hρ.1.1 hρ.2)
    (fun i => recv_dens V hV (pd_dens _ (hρ.1.1.eigenvectorBasis.orthonormal.1 i)))
    (recv_lin V _ _)

lemma yex_nonneg (V : Dilation I B E) (hV : IsIsometry V) (A : TwoLabelEnsemble I) (hA : A.Valid) :
    0 ≤ infoYEX V A := by
  obtain ⟨-, -, hp, hp1, hst⟩ := hA
  unfold infoYEX entropyEX
  rw [sub_nonneg]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases h0 : A.px x = 0
  · have hz : ∀ y, A.prob x y = 0 := fun y =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hp x y)).1 h0 y (Finset.mem_univ y)
    simp [h0, hz]
  · have hpos : 0 < A.px x := lt_of_le_of_ne (Finset.sum_nonneg fun y _ => hp x y) (Ne.symm h0)
    have hin : A.inputX x = ∑ y, ((A.prob x y / A.px x : ℝ) : ℂ) • A.state x y := by
      unfold TwoLabelEnsemble.inputX; rw [if_neg h0]
    have h := conc (complementaryChannel V) (fun y => A.prob x y / A.px x) (A.state x)
      (fun y => div_nonneg (hp x y) hpos.le) (by rw [← Finset.sum_div]; exact div_self h0)
      (fun y => comp_dens V hV (hst x y)) (comp_lin V _ _)
    rw [← hin] at h
    have h2 := mul_le_mul_of_nonneg_left h hpos.le
    have h3 : A.px x * ∑ y, A.prob x y / A.px x * vnEntropy (complementaryChannel V (A.state x y)) =
        ∑ y, A.prob x y * vnEntropy (complementaryChannel V (A.state x y)) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun y _ => ?_; field_simp
    rw [h3] at h2
    exact h2

theorem pub_dir (V : Dilation I B E) (hV : PhysicalDilation V) :
    EqualMax (values (fun A => infoXYB V A - infoYEX V A)) (pureSingleValues (infoXB V)) := by
  have hiso : IsIsometry V := hV.2.2.2
  obtain ⟨q, σ, hq, hq1, hσ, hmax⟩ := X6AT.att _ _ (g_cont V hiso) (g_cont V hiso)
  set M := vnEntropy (receiverChannel V (∑ i, q i • σ i)) -
    ∑ i, q i * vnEntropy (receiverChannel V (σ i)) with hM
  have hXYB : ∀ A : TwoLabelEnsemble I, A.Valid → infoXYB V A ≤ M := by
    intro A hA
    obtain ⟨-, -, hp, hp1, hst⟩ := hA
    have h := attG (fun ρ => vnEntropy (receiverChannel V ρ)) (fun ρ => vnEntropy (receiverChannel V ρ))
      hmax (T := Fin A.nx × Fin A.ny) (fun t => A.prob t.1 t.2)
      (fun t => A.state t.1 t.2) (fun t => hp _ _) (by rw [Fintype.sum_prod_type]; exact hp1)
      (fun t => hst _ _)
    unfold infoXYB entropyB
    rw [avg_eq]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
    exact h
  -- the pure refinement of the optimal ensemble
  let T := Fin (X6AT.KK I) × I
  let e := (Fintype.equivFin T).symm
  let hh := fun k => (hσ k).1.1
  let lam : T → ℝ := fun t => q t.1 * (hh t.1).eigenvalues t.2
  let psi : T → EuclideanSpace ℂ I := fun t => (hh t.1).eigenvectorBasis t.2
  have hlam : ∀ t, 0 ≤ lam t := fun t => mul_nonneg (hq _) ((hσ t.1).1.eigenvalues_nonneg _)
  have hlam1 : ∑ t, lam t = 1 := by
    simp only [lam, T, Fintype.sum_prod_type, ← Finset.mul_sum]
    simp only [fun k => eig_sum' (hh k) (hσ k).2, mul_one]; exact hq1
  have hpsi : ∀ t, ‖psi t‖ = 1 := fun t => (hh t.1).eigenvectorBasis.orthonormal.1 t.2
  let A2 : TwoLabelEnsemble I := ⟨Fintype.card T, 1, fun x _ => lam (e x),
    fun x _ => pureDensity (psi (e x))⟩
  have hA2 : A2.Valid := by
    refine ⟨Fintype.card_pos, by simp [A2], fun x _ => hlam _, ?_, fun x _ => pd_dens _ (hpsi _)⟩
    simp only [A2, Fin.sum_univ_one]
    rw [Equiv.sum_comp e lam]; exact hlam1
  have hpure : A2.Pure := fun x _ => ⟨psi (e x), hpsi _, rfl⟩
  have havg : A2.average = ∑ k, q k • σ k := by
    rw [avg_eq]
    simp only [A2, Fin.sum_univ_one]
    rw [Equiv.sum_comp e (fun t => lam t • pureDensity (psi t))]
    simp only [lam, T, Fintype.sum_prod_type, mul_smul, ← Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    conv_rhs => rw [spec_sum' (hh k)]
    simp only [Complex.coe_smul]
    rfl
  have hv2 : M ≤ infoXYB V A2 := by
    unfold infoXYB entropyB
    rw [havg]
    simp only [A2, Fin.sum_univ_one]
    rw [Equiv.sum_comp e (fun t => lam t * vnEntropy (receiverChannel V (pureDensity (psi t))))]
    simp only [lam, T, Fintype.sum_prod_type, mul_assoc, ← Finset.mul_sum]
    have := fun k => mul_le_mul_of_nonneg_left (refine_ent V hiso (hσ k)) (hq k)
    have h := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => this k
    rw [hM]; linarith
  have hv : infoXYB V A2 = M := le_antisymm (hXYB A2 hA2) hv2
  have hyex : infoYEX V A2 = 0 := by
    unfold infoYEX entropyEX
    rw [single_sum A2 rfl (fun ρ => vnEntropy (complementaryChannel V ρ))]; ring
  refine ⟨M, ⟨⟨A2, hA2, by show M = infoXYB V A2 - infoYEX V A2; rw [hyex, hv, sub_zero]⟩, ?_⟩,
    ⟨⟨A2, hA2, rfl, hpure, by rw [single_eq V A2 hA2 rfl, hv]⟩, ?_⟩⟩
  · rintro z ⟨A, hA, rfl⟩
    have := yex_nonneg V hiso A hA
    have := hXYB A hA
    linarith
  · rintro z ⟨A, hA, h1, -, rfl⟩
    rw [single_eq V A hA h1]; exact hXYB A hA

end X6P24


/-! Claimed50.P24: degradable dilations have nonnegative coherent information. -/

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

/-- Kraus operators of the receiver map. -/
def kB (V : Dilation I B E) : E → Matrix B I ℂ := fun e => of fun b a => V (b, e) a
/-- Kraus operators of the complementary map. -/
def kE (V : Dilation I B E) : B → Matrix E I ℂ := fun b => of fun e a => V (b, e) a

lemma kB_iso (V : Dilation I B E) (hV : IsIsometry V) : ∑ e, (kB V e)ᴴ * kB V e = 1 := by
  unfold IsIsometry at hV
  rw [← hV]
  ext a a'
  simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, kB, of_apply,
    Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma recv_kraus (V : Dilation I B E) : receiverChannel V = krausApply (kB V) := by
  funext ρ
  ext b b'
  simp only [receiverChannel, traceRight, krausApply, of_apply, Matrix.sum_apply, mul_apply,
    conjTranspose_apply, kB, Fintype.sum_prod_type]

lemma comp_kraus (V : Dilation I B E) : complementaryChannel V = krausApply (kE V) := by
  funext ρ
  ext e e'
  simp only [complementaryChannel, traceLeft, krausApply, of_apply, Matrix.sum_apply, mul_apply,
    conjTranspose_apply, kE, Fintype.sum_prod_type]

lemma compB (V : Dilation I B E) (σ : Matrix I I ℂ) :
    X6CH.comp (kB V) σ = complementaryChannel V σ := by
  ext e e'
  simp only [X6CH.comp, complementaryChannel, traceLeft, of_apply, Matrix.trace, Matrix.diag,
    mul_apply, conjTranspose_apply, kB, Fintype.sum_prod_type]

lemma compE (V : Dilation I B E) (σ : Matrix I I ℂ) :
    X6CH.comp (kE V) σ = receiverChannel V σ := by
  ext b b'
  simp only [X6CH.comp, receiverChannel, traceRight, of_apply, Matrix.trace, Matrix.diag,
    mul_apply, conjTranspose_apply, kE, Fintype.sum_prod_type]

/-- degradable ⇒ `S(E) ≤ S(B)` for every input density. -/
theorem deg_le (V : Dilation I B E) (hV : IsIsometry V) (hDeg : Degradable V) {σ : Matrix I I ℂ}
    (hσ : σ ∈ X6AT.Dens I) :
    vnEntropy (complementaryChannel V σ) ≤ vnEntropy (receiverChannel V σ) := by
  obtain ⟨T, hT, hTV⟩ := hDeg
  obtain ⟨m, F, hm, hF, rfl⟩ := X6CH.kraus_of_channel hT
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  set s := cfc Real.sqrt σ
  have hs : s * sᴴ = σ := X6CH.sqrt_sq hσ.1
  have hΨ : trace (s * sᴴ) = 1 := by rw [hs, hσ.2]
  obtain ⟨i1, -, -, -⟩ := X6CH.ineqs s (kB V) F (kB_iso V hV) hF hΨ
  simp only [hs] at i1
  have hFE : krausApply F ∘ krausApply (kB V) = krausApply (kE V) := by
    funext ρ
    simp only [Function.comp_apply, ← recv_kraus, ← comp_kraus, hTV]
  rw [← X6CH.idT_comp, hFE, X6CH.sc, compE, hs, compB, ← recv_kraus,
    hTV, comp_kraus] at i1
  rw [comp_kraus, recv_kraus]
  rw [recv_kraus] at i1
  linarith

end X6P24


/-! Claimed50.P24, Lemma 3: classical-quantum = public-private trade-off for degradable channels. -/

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

lemma px_nonneg (A : TwoLabelEnsemble I) (hA : A.Valid) (x : Fin A.nx) : 0 ≤ A.px x :=
  Finset.sum_nonneg fun y _ => hA.2.2.1 x y

lemma prob_zero (A : TwoLabelEnsemble I) (hA : A.Valid) {x : Fin A.nx} (h0 : A.px x = 0)
    (y : Fin A.ny) : A.prob x y = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hA.2.2.1 x y)).1 h0 y (Finset.mem_univ y)

lemma inputX_dens (A : TwoLabelEnsemble I) (hA : A.Valid) (x : Fin A.nx) :
    A.inputX x ∈ X6AT.Dens I := by
  unfold TwoLabelEnsemble.inputX
  split_ifs with h0
  · exact pd_dens _ (by simp [ket])
  · have hpos : 0 < A.px x := lt_of_le_of_ne (px_nonneg A hA x) (Ne.symm h0)
    simp only [Complex.coe_smul]
    exact X6AT.dens_avg _ _ (fun y => div_nonneg (hA.2.2.1 x y) hpos.le)
      (by rw [← Finset.sum_div]; exact div_self h0) (hA.2.2.2.2 x)

lemma avg_inputX (A : TwoLabelEnsemble I) (hA : A.Valid) :
    A.average = ∑ x, A.px x • A.inputX x := by
  rw [avg_eq]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h0 : A.px x = 0
  · simp [h0, prob_zero A hA h0]
  · unfold TwoLabelEnsemble.inputX
    rw [if_neg h0, Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Complex.coe_smul, smul_smul]
    congr 1
    field_simp

/-- the per-label cost in the classical-quantum objective. -/
def hF (V : Dilation I B E) (mu : ℝ) (ρ : Matrix I I ℂ) : ℝ :=
  vnEntropy (receiverChannel V ρ) -
    (1 + mu) * (vnEntropy (receiverChannel V ρ) - vnEntropy (complementaryChannel V ρ))

lemma hF_cont (V : Dilation I B E) (hV : IsIsometry V) (mu : ℝ) :
    ContinuousOn (hF V mu) (X6AT.Dens I) :=
  (g_cont V hV).sub (continuousOn_const.mul (G_cont V hV))

lemma cq_eq (V : Dilation I B E) (mu : ℝ) (A : TwoLabelEnsemble I) :
    classicalQuantumObjective V mu A =
      vnEntropy (receiverChannel V A.average) - ∑ x, A.px x * hF V mu (A.inputX x) := by
  unfold classicalQuantumObjective infoXB entropyB entropyBX entropyEX hF
  have e : ∀ x, A.px x * (vnEntropy (receiverChannel V (A.inputX x)) - (1 + mu) *
      (vnEntropy (receiverChannel V (A.inputX x)) - vnEntropy (complementaryChannel V (A.inputX x)))) =
      A.px x * vnEntropy (receiverChannel V (A.inputX x)) - (1 + mu) *
      (A.px x * vnEntropy (receiverChannel V (A.inputX x)) -
        A.px x * vnEntropy (complementaryChannel V (A.inputX x))) := fun x => by ring
  simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

lemma pp_sub_cq (V : Dilation I B E) (mu : ℝ) (A : TwoLabelEnsemble I) :
    publicPrivateObjective V mu A = classicalQuantumObjective V mu A - (1 + mu) *
      ∑ x, ∑ y, A.prob x y * (vnEntropy (receiverChannel V (A.state x y)) -
        vnEntropy (complementaryChannel V (A.state x y))) := by
  unfold publicPrivateObjective classicalQuantumObjective infoYBX infoYEX
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

lemma pp_le_cq (V : Dilation I B E) (hV : IsIsometry V) (hDeg : Degradable V) (mu : ℝ)
    (hmu : 0 ≤ mu) (A : TwoLabelEnsemble I) (hA : A.Valid) :
    publicPrivateObjective V mu A ≤ classicalQuantumObjective V mu A := by
  rw [pp_sub_cq]
  have h : 0 ≤ ∑ x, ∑ y, A.prob x y * (vnEntropy (receiverChannel V (A.state x y)) -
      vnEntropy (complementaryChannel V (A.state x y))) :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (hA.2.2.1 x y) (sub_nonneg.2 (deg_le V hV hDeg (hA.2.2.2.2 x y)))
  nlinarith

lemma pd_conj (V : Dilation I B E) (ψ : EuclideanSpace ℂ I) :
    V * pureDensity ψ * Vᴴ = pureDensity (WithLp.toLp 2 (V *ᵥ (ψ : I → ℂ))) := by
  ext p q
  simp only [pureDensity, of_apply, mul_apply, conjTranspose_apply, mulVec, dotProduct,
    PiLp.toLp_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma pure_eq (V : Dilation I B E) (ψ : EuclideanSpace ℂ I) :
    vnEntropy (receiverChannel V (pureDensity ψ)) =
      vnEntropy (complementaryChannel V (pureDensity ψ)) := by
  unfold receiverChannel complementaryChannel
  rw [pd_conj]
  exact X6SSA.vn_pure_marginals _

theorem deg_tradeoffs (V : Dilation I B E) (hV : PhysicalDilation V) (hDeg : Degradable V)
    (mu : ℝ) (hmu : 0 ≤ mu) :
    EqualMax (singleValues (classicalQuantumObjective V mu))
      (values (publicPrivateObjective V mu)) := by
  have hiso : IsIsometry V := hV.2.2.2
  obtain ⟨q, σ, hq, hq1, hσ, hmax⟩ := X6AT.att _ _ (g_cont V hiso) (hF_cont V hiso mu)
  set M := vnEntropy (receiverChannel V (∑ i, q i • σ i)) - ∑ i, q i * hF V mu (σ i) with hM
  have hcq : ∀ A : TwoLabelEnsemble I, A.Valid → classicalQuantumObjective V mu A ≤ M := by
    intro A hA
    rw [cq_eq, avg_inputX A hA]
    exact attG (fun ρ => vnEntropy (receiverChannel V ρ)) (hF V mu) (q := q) (σ := σ) hmax (T := Fin A.nx) A.px A.inputX (px_nonneg A hA) hA.2.2.2.1
      (inputX_dens A hA)
  -- a single-label maximiser
  let A0 : TwoLabelEnsemble I := ⟨X6AT.KK I, 1, fun x _ => q x, fun x _ => σ x⟩
  have hA0 : A0.Valid := by
    refine ⟨by simp [A0], by simp [A0], fun x _ => hq x, ?_, fun x _ => hσ x⟩
    simp [A0, hq1]
  have v0 : classicalQuantumObjective V mu A0 = M := by
    rw [cq_eq, single_sum A0 rfl (hF V mu), avg_eq]
    simp [A0, hM]
  -- its pure spectral refinement
  let e := (Fintype.equivFin I).symm
  let hh := fun k => (hσ k).1.1
  let A2 : TwoLabelEnsemble I := ⟨X6AT.KK I, Fintype.card I,
    fun x y => q x * (hh x).eigenvalues (e y), fun x y => pureDensity ((hh x).eigenvectorBasis (e y))⟩
  have hpx : ∀ x, A2.px x = q x := by
    intro x
    simp only [TwoLabelEnsemble.px, A2, ← Finset.mul_sum]
    rw [Equiv.sum_comp e (fun i => (hh x).eigenvalues i), eig_sum' (hh x) (hσ x).2, mul_one]
  have hA2 : A2.Valid := by
    refine ⟨by simp [A2], Fintype.card_pos,
      fun x y => mul_nonneg (hq x) ((hσ x).1.eigenvalues_nonneg _), ?_,
      fun x y => pd_dens _ ((hh x).eigenvectorBasis.orthonormal.1 _)⟩
    have := fun x => hpx x
    simp only [TwoLabelEnsemble.px] at this
    simp only [this]; exact hq1
  have hin : ∀ x, q x ≠ 0 → A2.inputX x = σ x := by
    intro x hx
    unfold TwoLabelEnsemble.inputX
    rw [if_neg (by rw [hpx]; exact hx), hpx]
    conv_rhs => rw [spec_sum' (hh x)]
    rw [← Equiv.sum_comp e (fun i => (((hh x).eigenvalues i : ℝ) : ℂ) •
      pureDensity ((hh x).eigenvectorBasis i))]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [A2]
    congr 2
    field_simp
  have hterm : ∀ x, A2.px x * hF V mu (A2.inputX x) = q x * hF V mu (σ x) := by
    intro x
    by_cases hx : q x = 0
    · rw [hpx, hx, zero_mul, zero_mul]
    · rw [hpx, hin x hx]
  have hterm2 : ∀ x, A2.px x • A2.inputX x = q x • σ x := by
    intro x
    by_cases hx : q x = 0
    · rw [hpx, hx, zero_smul, zero_smul]
    · rw [hpx, hin x hx]
  have v2c : classicalQuantumObjective V mu A2 = M := by
    rw [cq_eq, avg_inputX A2 hA2]
    simp only [hterm, hterm2]
    rfl
  have v2 : publicPrivateObjective V mu A2 = M := by
    rw [pp_sub_cq, v2c]
    have : ∀ x y, A2.prob x y * (vnEntropy (receiverChannel V (A2.state x y)) -
        vnEntropy (complementaryChannel V (A2.state x y))) = 0 := by
      intro x y
      simp only [A2]
      rw [pure_eq, sub_self, mul_zero]
    simp [this]
  refine ⟨M, ⟨⟨A0, hA0, rfl, v0.symm⟩, ?_⟩, ⟨⟨A2, hA2, v2.symm⟩, ?_⟩⟩
  · rintro z ⟨A, hA, -, rfl⟩; exact hcq A hA
  · rintro z ⟨A, hA, rfl⟩; exact (pp_le_cq V hiso hDeg mu hmu A hA).trans (hcq A hA)

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

theorem solution (V : Dilation I B E) (hV : PhysicalDilation V)
    (hDeg : Degradable V) (mu : ℝ) (hmu : 0 ≤ mu) :
    EqualMax (singleValues (classicalQuantumObjective V mu))
      (values (publicPrivateObjective V mu)) :=
  X6P24.deg_tradeoffs V hV hDeg mu hmu

end
