-- Prove2me | solution 1 for WatrousTQI.unital_channels_compact_convex
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T18:40:11.741781+00:00
-- url     : https://prove2.me/submissions/7ce1c99d-5b7c-40c0-a10e-312a96c9954d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Module
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WatrousTQI_UnitalChannels

set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate BigOperators
open scoped ComplexOrder
namespace WatrousUnitalCompactAux20261112
open QAlgorithms
open scoped ComplexOrder
abbrev C (d : ℕ) := Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ
noncomputable def F (d : ℕ) : C d →ₗ[ℝ] Superop (Fin d) (Fin d) where
  toFun J X o p := ∑ i, ∑ j, X i j * J (o,i) (p,j)
  map_add' A B := by
    ext X o p
    change (∑ i, ∑ j, X i j * (A (o,i) (p,j) + B (o,i) (p,j))) =
      (∑ i, ∑ j, X i j * A (o,i) (p,j)) + (∑ i, ∑ j, X i j * B (o,i) (p,j))
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a A := by
    ext X o p
    change (∑ i, ∑ j, X i j * (a • A (o,i) (p,j))) = a • (∑ i, ∑ j, X i j * A (o,i) (p,j))
    simp_rw [mul_smul_comm, Finset.smul_sum]
noncomputable def CJ {d m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ) : C d :=
  ∑ j, Matrix.vecMulVec (fun p => E j p.1 p.2) (star (fun p => E j p.1 p.2))
def TL {d : ℕ} (J : C d) : Matrix (Fin d) (Fin d) ℂ := fun i j => ∑ o, J (o,i) (o,j)
lemma CJ_pos {d m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ) : (CJ E).PosSemidef := by
  unfold CJ
  exact Matrix.posSemidef_sum _ (fun i _ => Matrix.posSemidef_vecMulVec_self_star _)
lemma F_CJ {d m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ) : F d (CJ E) = krausApply E := by
  ext o p q
  change (∑ i, ∑ j, o i j * (CJ E) (p,i) (q,j)) = _
  simp only [ LinearMap.coe_mk, AddHom.coe_mk, CJ, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, krausApply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => enter [2, j]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  conv_rhs => enter [2, j]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring
lemma TL_CJ {d m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ) :
    TL (CJ E) = (∑ l, (E l)ᴴ * E l)ᵀ := by
  ext i j
  simp only [TL, CJ, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    Matrix.transpose_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun o _ => ?_
  ring
lemma CJ_exists {d : ℕ} (J : C d) (hJ : J.PosSemidef) :
    ∃ (m : ℕ) (E : Fin m → Matrix (Fin d) (Fin d) ℂ), J = CJ E := by
  obtain ⟨m,v,hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hJ
  refine ⟨m, fun j o i => v j (o,i), ?_⟩
  simpa [CJ] using hv
end WatrousUnitalCompactAux20261112

namespace WatrousPSDCompactAux20261112

theorem closed_psd {E : Type*} [Fintype E] :
    IsClosed {X : Matrix E E ℂ | X.PosSemidef} := by
  have e : {X : Matrix E E ℂ | X.PosSemidef} =
      {X | Xᴴ = X} ∩ ⋂ x : E → ℂ, {X | 0 ≤ (star x ⬝ᵥ (X *ᵥ x)).re ∧ (star x ⬝ᵥ (X *ᵥ x)).im = 0} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Matrix.posSemidef_iff_dotProduct_mulVec,
      Matrix.IsHermitian, Complex.nonneg_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun x => ⟨(h2 x).1, (h2 x).2.symm⟩⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun x => ⟨(h2 x).1, (h2 x).2.symm⟩⟩
  rw [e]
  refine IsClosed.inter (isClosed_eq (Continuous.matrix_conjTranspose continuous_id) continuous_id) ?_
  refine isClosed_iInter fun x => ?_
  have hc : Continuous fun X : Matrix E E ℂ => star x ⬝ᵥ (X *ᵥ x) := by
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  exact IsClosed.inter (isClosed_le continuous_const (Complex.continuous_re.comp hc))
    (isClosed_eq (Complex.continuous_im.comp hc) continuous_const)

theorem entry_bound {E : Type*} [Fintype E] [DecidableEq E] (X : Matrix E E ℂ) (hX : X.PosSemidef) (i j : E) :
    ‖X i j‖ ≤ X.trace.re := by
  obtain ⟨m, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  have hent : ∀ a b, X a b = ∑ k, v k a * conj (v k b) := by
    intro a b; rw [hv, Matrix.sum_apply]; simp [Matrix.vecMulVec_apply]
  have htr : X.trace.re = ∑ k, ∑ a, Complex.normSq (v k a) := by
    rw [Matrix.trace, Complex.re_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.diag, hent, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re]
  rw [hent, htr]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, Complex.norm_conj]
  have h1 : ‖v k i‖ * ‖v k j‖ ≤ (Complex.normSq (v k i) + Complex.normSq (v k j)) / 2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖v k i‖ - ‖v k j‖)]
  by_cases hij : i = j
  · subst hij
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have := Finset.sum_nonneg (s := Finset.univ.erase i) fun a _ => Complex.normSq_nonneg (v k a)
    linarith
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)]
    have := Finset.sum_nonneg (s := (Finset.univ.erase i).erase j) fun a _ => Complex.normSq_nonneg (v k a)
    have h2 := Complex.normSq_nonneg (v k i)
    have h3 := Complex.normSq_nonneg (v k j)
    linarith

theorem main {E : Type*} [Fintype E] [DecidableEq E] (alpha : ℝ) (halpha : 0 ≤ alpha) :
    IsCompact {X : Matrix E E ℂ | X.PosSemidef ∧ X.trace.re ≤ alpha} ∧
      IsCompact {X : Matrix E E ℂ | X.PosSemidef ∧ X.trace.re = alpha} := by
  have hK : IsCompact (Set.univ.pi fun _ : E => Set.univ.pi fun _ : E => Metric.closedBall (0 : ℂ) alpha) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 alpha
  have htr : Continuous fun X : Matrix E E ℂ => X.trace.re := by
    simp only [Matrix.trace, Matrix.diag]; fun_prop
  have h1 : IsCompact {X : Matrix E E ℂ | X.PosSemidef ∧ X.trace.re ≤ alpha} := by
    refine hK.of_isClosed_subset ?_ ?_
    · exact IsClosed.inter closed_psd (isClosed_le htr continuous_const)
    · rintro X ⟨hX, ht⟩
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
      intro i j
      exact (entry_bound X hX i j).trans ht
  refine ⟨h1, h1.of_isClosed_subset ?_ ?_⟩
  · exact IsClosed.inter closed_psd (isClosed_eq htr continuous_const)
  · rintro X ⟨hX, ht⟩; exact ⟨hX, ht.le⟩

end WatrousPSDCompactAux20261112

namespace WatrousUnitalCompactAux20261112
noncomputable def S (d : ℕ) : Set (C d) := {J | J.PosSemidef ∧ TL J = 1 ∧ F d J 1 = 1}
lemma image_S (d : ℕ) : F d '' S d = WatrousTQI.unitalChannels d := by
  classical
  ext Φ
  constructor
  · rintro ⟨J,⟨hp,ht,hu⟩,rfl⟩
    obtain ⟨m,E,rfl⟩ := CJ_exists J hp
    refine ⟨⟨m,E,?_,?_⟩,hu⟩
    · have h := congrArg Matrix.transpose ht
      simpa [TL_CJ, QAlgorithms.IsKrausFamily] using h
    · intro X
      exact congrFun (F_CJ E) X
  · rintro ⟨⟨m,E,hE,hΦ⟩,hu⟩
    have heq : F d (CJ E) = Φ := by rw [F_CJ]; exact (funext hΦ).symm
    refine ⟨CJ E,⟨CJ_pos E,?_,?_⟩,heq⟩
    · rw [TL_CJ,hE,Matrix.transpose_one]
    · rw [heq]; exact hu
lemma F_cont (d : ℕ) : Continuous (F d) := by
  change Continuous (fun J : C d => fun (X : Matrix (Fin d) (Fin d) ℂ) (o p : Fin d) => ∑ i, ∑ j, X i j * J (o,i) (p,j))
  fun_prop
lemma TL_cont (d : ℕ) : Continuous (TL (d := d)) := by
  change Continuous (fun J : C d => fun i j => ∑ o, J (o,i) (o,j))
  fun_prop
lemma S_compact (d : ℕ) : IsCompact (S d) := by
  classical
  have hc := (WatrousPSDCompactAux20261112.main (E := Fin d × Fin d) (d : ℝ) (Nat.cast_nonneg d)).2
  apply hc.of_isClosed_subset
  · exact IsClosed.inter WatrousPSDCompactAux20261112.closed_psd (IsClosed.inter
      (isClosed_eq (TL_cont d) continuous_const)
      (isClosed_eq ((continuous_apply 1).comp (F_cont d)) continuous_const))
  · rintro J ⟨hp,ht,hu⟩
    refine ⟨hp,?_⟩
    have hh : (TL J).trace = J.trace := by
      simp only [Matrix.trace, Matrix.diag, TL, Fintype.sum_prod_type]
      exact Finset.sum_comm
    rw [← hh,ht,Matrix.trace_one]
    simp
lemma S_convex (d : ℕ) : Convex ℝ (S d) := by
  classical
  intro J hJ L hL a b ha hb hab
  refine ⟨(hJ.1.smul ha).add (hL.1.smul hb),?_,?_⟩
  · have heq : TL (a • J + b • L) = a • TL J + b • TL L := by
      ext i j
      simp [TL, Finset.sum_add_distrib, Finset.smul_sum]
    rw [heq,hJ.2.1,hL.2.1,← add_smul,hab,one_smul]
  · rw [map_add,map_smul,map_smul]
    change a • F d J 1 + b • F d L 1 = 1
    rw [hJ.2.2,hL.2.2,← add_smul,hab,one_smul]
lemma span_finite (d : ℕ) : FiniteDimensional ℝ (Submodule.span ℝ (WatrousTQI.unitalChannels d)) := by
  have hle : Submodule.span ℝ (WatrousTQI.unitalChannels d) ≤ LinearMap.range (F d) := by
    apply Submodule.span_le.mpr
    intro Φ hΦ
    rw [← image_S] at hΦ
    obtain ⟨J,hJ,rfl⟩ := hΦ
    exact ⟨J,rfl⟩
  exact Submodule.finiteDimensional_of_le hle
end WatrousUnitalCompactAux20261112

open WatrousTQI


theorem solution (d : ℕ) (hd : 0 < d) :
    IsCompact (unitalChannels d) ∧ Convex ℝ (unitalChannels d) ∧
      FiniteDimensional ℝ (Submodule.span ℝ (unitalChannels d)) := by
  rw [← WatrousUnitalCompactAux20261112.image_S d]
  exact ⟨(WatrousUnitalCompactAux20261112.S_compact d).image (WatrousUnitalCompactAux20261112.F_cont d),
    (WatrousUnitalCompactAux20261112.S_convex d).linear_image (WatrousUnitalCompactAux20261112.F d), by
      rw [WatrousUnitalCompactAux20261112.image_S d]
      exact WatrousUnitalCompactAux20261112.span_finite d⟩
