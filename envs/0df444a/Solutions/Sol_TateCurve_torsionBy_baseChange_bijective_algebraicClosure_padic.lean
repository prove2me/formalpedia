-- Prove2me | solution 1 for TateCurve.torsionBy_baseChange_bijective_algebraicClosure_padic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9f34bc5b-5498-5525-8fbf-1e94acbfc26f

import Mathlib
import Definitions.Def_TateCurve_TorsionParametrization
import Definitions.Def_FLTPrelim_GaloisRep
import Theorems.Thm_WeierstrassCurve_Affine_Point_isIntegral_of_smul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TateCurve_torsionBy_baseChange_bijective_algebraicClosure_padic
p2m_attr_erase "simp" "WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

open scoped NNReal WeierstrassCurve.Affine
p2m_open "WeierstrassCurve WeierstrassCurve.Affine.Point TateCurve P2MW.S_TateCurve_torsionBy_baseChange_bijective_algebraicClosure_padic.TateCurve"

set_option maxHeartbeats 4800000

namespace TateCurve
p2m_export "TateCurve" "term summable_term coeffSum a₄ a₆ curve isElliptic map_curve"
namespace C2c4Aux
p2m_open "TateCurve"

variable {K₁ : Type*} [NontriviallyNormedField K₁] [IsUltrametricDist K₁]
variable {K₂ : Type*} [NontriviallyNormedField K₂] [IsUltrametricDist K₂]

theorem map_tsum_of_summable₂ {ι : Type*} (σ : K₁ →+* K₂) (hσ : Isometry ⇑σ) {f : ι → K₁}
    (hf : Summable f) : σ (∑' i, f i) = ∑' i, σ (f i) := by
  have h := hf.hasSum.map σ hσ.continuous
  simpa [Function.comp] using h.tsum_eq.symm

theorem map_term₂ (σ : K₁ →+* K₂) (q : K₁) (c : ℕ → ℕ) (n : ℕ) :
    σ (term c q n) = term c (σ q) n := by
  simp only [term, map_mul, map_natCast, map_div₀, map_pow, map_sub, map_one]

variable [CompleteSpace K₁] [CompleteSpace K₂]

theorem map_coeffSum₂ (σ : K₁ →+* K₂) (hσ : Isometry ⇑σ) {q : K₁} (hq : ‖q‖₊ < 1) (c : ℕ → ℕ) :
    σ (coeffSum c q) = coeffSum c (σ q) := by
  rw [coeffSum, coeffSum, map_tsum_of_summable₂ σ hσ (summable_term c hq)]
  exact tsum_congr fun n => map_term₂ σ q c n

theorem map_a₄₂ (σ : K₁ →+* K₂) (hσ : Isometry ⇑σ) {q : K₁} (hq : ‖q‖₊ < 1) :
    σ (a₄ q) = a₄ (σ q) := by
  simp only [a₄, map_neg]
  exact congrArg Neg.neg (map_coeffSum₂ σ hσ hq _)

theorem map_a₆₂ (σ : K₁ →+* K₂) (hσ : Isometry ⇑σ) {q : K₁} (hq : ‖q‖₊ < 1) :
    σ (a₆ q) = a₆ (σ q) := by
  simp only [a₆, map_neg]
  exact congrArg Neg.neg (map_coeffSum₂ σ hσ hq _)

theorem map_curve₂ (σ : K₁ →+* K₂) (hσ : Isometry ⇑σ) {q : K₁} (hq : ‖q‖₊ < 1) :
    (curve q).map σ = curve (σ q) := by
  ext <;> simp [curve, WeierstrassCurve.map, map_a₄₂ σ hσ hq, map_a₆₂ σ hσ hq]

theorem ps_congr {K : Type*} [CommRing K] {W : WeierstrassCurve.Affine K} {x x' y y' : K}
    (hx : x = x') (hy : y = y')
    (h : W.Nonsingular x y) (h' : W.Nonsingular x' y') :
    (WeierstrassCurve.Affine.Point.some x y h : W.Point)
      = WeierstrassCurve.Affine.Point.some x' y' h' := by
  subst hx; subst hy; rfl

end TateCurve.C2c4Aux

open TateCurve.C2c4Aux

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (qT : ℚ_[p]) (hqT0 : qT ≠ 0) (hqT1 : ‖qT‖₊ < 1)
    (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [CharZero K] [IsAlgClosed K] [Algebra ℚ_[p] K]
    (hiso : ∀ x : ℚ_[p], ‖algebraMap ℚ_[p] K x‖ = ‖x‖)
    (ι : AlgebraicClosure ℚ_[p] →ₐ[ℚ_[p]] K) :
    letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
    letI : DecidableEq K := Classical.decEq _
    ((TateCurve.curve qT).map (algebraMap ℚ_[p] K) = TateCurve.curve (algebraMap ℚ_[p] K qT)) ∧
    Function.Bijective
      (fun P : Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point p =>
        (⟨WeierstrassCurve.Affine.Point.map ι
            (P : ((TateCurve.curve qT)⁄(AlgebraicClosure ℚ_[p])).Point),
          by
            rw [Submodule.mem_torsionBy_iff, ← AddMonoidHom.map_zsmul,
              (Submodule.mem_torsionBy_iff _ _).mp P.property, AddMonoidHom.map_zero]⟩ :
        Submodule.torsionBy ℤ ((TateCurve.curve qT)⁄K).Point p)) := by
  letI : DecidableEq (AlgebraicClosure ℚ_[p]) := Classical.decEq _
  letI : DecidableEq K := Classical.decEq _
  have hp : p.Prime := Fact.out

  have hf_isom : Isometry ⇑(algebraMap ℚ_[p] K) := AddMonoidHomClass.isometry_of_norm _ hiso
  have hιinj : Function.Injective ⇑ι := RingHom.injective ι.toRingHom

  refine ⟨map_curve₂ (algebraMap ℚ_[p] K) hf_isom hqT1, ?_, ?_⟩

  · intro P Q hPQ
    exact Subtype.ext (Affine.Point.map_injective ι (congrArg Subtype.val hPQ))

  · rintro ⟨Q, hQ⟩
    rcases Q with _ | ⟨x, y, hns⟩
    ·
      exact ⟨0, Subtype.ext (_root_.map_zero _)⟩
    ·

      haveI : (curve qT).IsElliptic := TateCurve.isElliptic hqT0 hqT1
      have hp_ne : ((p : ℤ) : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero

      have hQ' : (p : ℤ) • (Affine.Point.some x y hns : ((curve qT)⁄K).Point) = 0 :=
        (Submodule.mem_torsionBy_iff _ _).mp hQ
      have hxy := WeierstrassCurve.Affine.Point.isIntegral_of_smul_eq_zero
        (F := ℚ_[p]) (L := K) (W := curve qT) (n := (p : ℤ)) hp_ne hns hQ'

      obtain ⟨x', hx'⟩ := hxy.1.mem_range_algHom_of_minpoly_splits (IsAlgClosed.splits _) ι
      obtain ⟨y', hy'⟩ := hxy.2.mem_range_algHom_of_minpoly_splits (IsAlgClosed.splits _) ι

      replace hx' : ι x' = x := hx'
      replace hy' : ι y' = y := hy'

      have hns' : ((curve qT)⁄(AlgebraicClosure ℚ_[p])).Nonsingular x' y' := by
        have hnsK : ((curve qT)⁄K).Nonsingular (ι x') (ι y') := hx' ▸ hy' ▸ hns
        exact (WeierstrassCurve.Affine.baseChange_nonsingular
          (W := (curve qT).toAffine) hιinj x' y').mp hnsK

      refine ⟨⟨Affine.Point.some x' y' hns', ?_⟩, ?_⟩
      ·
        rw [Submodule.mem_torsionBy_iff]
        apply Affine.Point.map_injective ι
        rw [AddMonoidHom.map_zsmul, _root_.map_zero, Affine.Point.map_some, ps_congr hx' hy' _ hns]
        exact hQ'
      ·
        exact Subtype.ext ((Affine.Point.map_some ι hns').trans (ps_congr hx' hy' _ hns))

end S_TateCurve_torsionBy_baseChange_bijective_algebraicClosure_padic
end P2MW
export P2MW.S_TateCurve_torsionBy_baseChange_bijective_algebraicClosure_padic (solution)
