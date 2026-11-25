-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartResidue_proof_28fdecb34b79
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:52:59.041927+00:00
-- url     : https://prove2.me/submissions/f65b7176-552f-48bd-997c-e5f7df0cdf48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartResidue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartDehom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartResidue
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_natCard_eq_pow_length_of_finiteType_f3a3739dc0cd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
namespace GroundTheory.Heights₂.Heights
namespace OrbitChartResidue
theorem _root_.solution (hM : OrbitChartMax.Statement) (hQ : OrbitChartQuot.Statement)
    (hD : OrbitChartDehom.Statement) : OrbitChartResidue.Statement := by
  intro ι _ _ _ n A x s hx hs V hV c hc
  have hPV : orbitIdeal x ≤ V := le_sup_left.trans hV.1.1.2
  have hrel : Geo.IsRelevant V := hV.2
  have hxc : ∀ c' : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) → ∀ k, x k (c' k) ≠ 0 := by
    intro c' h k h0
    apply h k
    apply hPV
    rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, aeval_X]
    simp [flatCone, h0]
  set i : (k : ι) → Fin (n k + 1) := fun k ↦ (hrel k).choose
  have hi : ∀ k, (X ⟨k, i k⟩ : MvPolynomial (Coord n) ℤ) ∉ V := fun k ↦ (hrel k).choose_spec
  obtain ⟨eQ⟩ := hQ ι n x c (hxc c hc) V hPV
  obtain ⟨hchar, ⟨eD⟩⟩ := hD ι n A x s hx hs V hV i c hi hc
  set J := V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, i k⟩ : MvPolynomial (Coord n) ℤ) - 1)
  let e : (chartRing x c ⧸ chartPoint x c V) ≃+* (MvPolynomial (Coord n) ℤ ⧸ J) := eQ.trans eD.symm
  have := hM ι n A x s hx hs V hV c hc
  have hfield : IsField (MvPolynomial (Coord n) ℤ ⧸ J) :=
    MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance)
      e.symm.toMulEquiv
  have : J.IsMaximal := (Ideal.Quotient.maximal_ideal_iff_isField_quotient J).mpr hfield
  let : Field (MvPolynomial (Coord n) ℤ ⧸ J) := Ideal.Quotient.field J
  have hft : Algebra.FiniteType ℤ (MvPolynomial (Coord n) ℤ ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ J)
      (Ideal.Quotient.mkₐ_surjective ℤ J)
  have : CharP (MvPolynomial (Coord n) ℤ ⧸ J) (Geo.charOf V) := by
    constructor
    intro a
    have hJC : ∀ b : ℤ, ((b : MvPolynomial (Coord n) ℤ ⧸ J) = 0 ↔ b ∈ V.comap (C : ℤ →+* _)) := by
      intro b
      rw [(map_intCast (Ideal.Quotient.mk J) b).symm.trans (congrArg _ (eq_intCast C b).symm),
        Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hchar]
    rw [← Int.cast_natCast, hJC, Submodule.IsPrincipal.mem_iff_generator_dvd, ← Int.natAbs_dvd,
      Int.natCast_dvd_natCast]
    rfl
  obtain ⟨-, hcard⟩ := @natCard_eq_pow_length_of_finiteType (MvPolynomial (Coord n) ℤ ⧸ J) _
    (by convert hft using 1 <;> rfl) (Geo.charOf V) _
  have hgeo : Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 =
      ((Module.length ℤ (MvPolynomial (Coord n) ℤ ⧸ J)).toNat : ℤ) := by
    simp only [Geo.geoNum, dif_pos hrel]
    rfl
  rw [hgeo, Nat.card_congr e.toEquiv, hcard, Nat.cast_pow, Real.log_pow]
  push_cast
  ring
end OrbitChartResidue
end GroundTheory.Heights₂.Heights
