-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocLengthSum_proof_c7e7c781621f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:02:44.19282+00:00
-- url     : https://prove2.me/submissions/dcb05de3-1047-47c1-893b-a51e6b8487c7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocResidueDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFibreOverFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLocRingDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PFiniteAlgebraLengthSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocLengthSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_FiniteAlgebraLengthSum_proof_0bd46f3576aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_locToSemiloc_coe_05d28c336456
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_semiToLoc_coe_6afe5d0b143c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
namespace GroundTheory.Heights₂.Heights.Inter
namespace SemilocLengthSum
theorem _root_.solution (h₁ : SemilocFinite.Statement) (h₂ : SemilocMaxIdeals.Statement)
    (h₃ : SemilocResidueDeg.Statement) (h₄ : FibreDivSupp.Statement) (h₅ : LocRingDimOne.Statement)
    (h₆ : FibreOverFinite.Statement) :
    SemilocLengthSum.Statement := by
  classical
  intro K _ ι _ K' _ ι' _ κ v P' n s t α W E hv hP' y hPn hs ht hsP hW htW hy hE
  have := hP'.2.1.1
  have := imageZ_isPrime_of_prime v P'
  let _ := (locToSemiloc hv P' W).toAlgebra
  have hfin := h₆ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW
  obtain ⟨hmax, hinj, hcov⟩ := h₂ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW
  have : IsLocalRing (locRing (imageZ v P') W) := (h₅ K ι (imageZ v P') s α W hPn.2.1 hs hsP hW).2.1
  have : Module.Finite (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W)) :=
    (h₁ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW).1
  let _ : Fintype (fibreOver v P' W) := hfin.fintype
  have hloc : ∀ W' : fibreOver v P' W, IsLocalRing (locRing P' W'.1) := fun W' =>
    haveI := W'.2.1.1; regularityLocalFlat_holds.isLocalRing W'.2.2.1
  let _ : ∀ W' : fibreOver v P' W, Algebra (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1) :=
    fun W' => (semiToLoc P' _ W'.1 W'.2).toAlgebra
  have key := FieldNumbers.FiniteAlgebraLengthSum.proof.{0} (locRing (imageZ v P') W) (semiLocRing P' (fibreOver v P' W))
    (fibreOver v P' W) (fun W' => semiMaxIdeal P' _ W'.1 W'.2) (fun W' => (hmax W'.1 W'.2).1)
    (fun W₁ W₂ h => Subtype.ext (hinj W₁.1 W₂.1 W₁.2 W₂.2 h))
    (fun M hM => by obtain ⟨W', hW', h⟩ := hcov M hM; exact ⟨⟨W', hW'⟩, @h (hloc ⟨W', hW'⟩)⟩)
    (fun W' => locRing P' W'.1) (fun W' => (hmax W'.1 W'.2).2) y

  refine ⟨hfin, ?_⟩
  have hyne : (y : FractionRing (MRing ι ⧸ imageZ v P')) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hy
    exact hsP hy
  have hs' : rename v s ∉ P' := hsP
  have hterm : ∀ W' : fibreOver v P' W,
      Ring.ord (locRing P' W'.1) (algebraMap (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1)
          (algebraMap (locRing (imageZ v P') W) _ y)) *
        Module.length (locRing (imageZ v P') W)
          (semiLocRing P' (fibreOver v P' W) ⧸ semiMaxIdeal P' _ W'.1 W'.2) ≠ ⊤ ∧
      (((Ring.ord (locRing P' W'.1) (algebraMap (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1)
          (algebraMap (locRing (imageZ v P') W) _ y)) *
        Module.length (locRing (imageZ v P') W)
          (semiLocRing P' (fibreOver v P' W) ⧸ semiMaxIdeal P' _ W'.1 W'.2)).toNat : ℕ) : ℤ) =
        if rename v s ∈ W'.1 then
          ((Module.length (locRing P' W'.1) (locRing P' W'.1 ⧸ locIdeal P' W'.1 (fracMapZ v P' y))).toNat : ℤ) *
            E W'.1 else 0 := by
    intro W'
    obtain ⟨hW'p, hPW', hW'i⟩ := W'.2
    have := hW'p.1
    set x := algebraMap (semiLocRing P' (fibreOver v P' W)) (locRing P' W'.1)
      (algebraMap (locRing (imageZ v P') W) _ y) with hxdef
    have hx : (x : FractionRing (MRing ι' ⧸ P')) = fracMapZ v P' y := by
      rw [hxdef, RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, semiToLoc_coe, locToSemiloc_coe]
    have hord : Ring.ord (locRing P' W'.1) x =
        Module.length (locRing P' W'.1) (locRing P' W'.1 ⧸ locIdeal P' W'.1 (fracMapZ v P' y)) := by
      have hI : locIdeal P' W'.1 (fracMapZ v P' y) = Ideal.span {x} := by
        rw [locIdeal, ← hx]
        congr 1
        ext z
        simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
        exact Subtype.ext_iff.symm
      rw [Ring.ord, hI]
    split_ifs with hsW'
    · obtain ⟨G', J', hJ', hEW'⟩ := hE W'.1 W'.2 hsW'
      obtain ⟨d, hd, hdE⟩ := h₃ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW W'.1 W'.2 G' J' hJ'
      have hdiv : W'.1 ∈ divSupp P' (rename v s) :=
        ((h₄ K ι K' ι' κ v P' n s α W hv hP' hPn hs hsP hW W'.1).1 ⟨W'.2, hsW'⟩).1
      obtain ⟨hN, -, hdim⟩ := h₅ K' ι' P' (rename v s) (Function.extend κ α 0) W'.1 hP'.2.1
        (rename_isMultiHomog hv hs) hs' hdiv
      have : Ring.KrullDimLE 1 (locRing P' W'.1) := by
        rw [Ring.krullDimLE_iff, hdim]
        rfl
      have hx0 : x ≠ 0 := fun h =>
        (map_ne_zero (fracMapZ v P')).mpr hyne (by rw [← hx, h, ZeroMemClass.coe_zero])
      have hfinord := Ring.ord_ne_top (R := locRing P' W'.1) (mem_nonZeroDivisors_of_ne_zero hx0)
      rw [hd, ← hord]
      refine ⟨WithTop.mul_ne_top hfinord (ENat.natCast_ne_top d), ?_⟩
      rw [ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_mul, hdE, hEW']
    · have ht' : rename v t ∉ W'.1 := fun h => htW (hW'i ▸ h)
      have hxe : (x : FractionRing (MRing ι' ⧸ P')) * regularityLocalFlat_holds.fracHom P' (rename v t) =
          regularityLocalFlat_holds.fracHom P' (rename v s) := by
        rw [hx, regularityLocalFlat_holds.fracHom_apply, regularityLocalFlat_holds.fracHom_apply, ← fracMapZ_algebraMap, ← fracMapZ_algebraMap,
          ← map_mul, hy]
      have hu : IsUnit x := (regularityLocalFlat_holds.isUnit_iff hPW' x (rename_isMultiHomog hv hs) (rename_isMultiHomog hv ht) ht'
        hxe).mpr hsW'
      rw [Ring.ord_of_isUnit hu, zero_mul]
      simp
  have hset : {W' | W' ∈ fibreOver v P' W ∧ rename v s ∈ W'} =
      ↑(hfin.toFinset.filter (fun W' => rename v s ∈ W')) := by
    ext
    simp
  have hsum := ENat.sum_ne_top.mpr fun W' (_ : W' ∈ Finset.univ) => (hterm W').1
  rw [key]
  refine ⟨_, (ENat.natCast_toNat hsum).symm, ?_⟩
  rw [ENat.toNat_sum fun W' _ => (hterm W').1, Nat.cast_sum, hset, finsum_mem_coe_finset, Finset.sum_filter,
    Finset.sum_subtype (F := hfin.fintype) hfin.toFinset (fun _ => Set.Finite.mem_toFinset hfin)]
  exact Finset.sum_congr rfl fun W' _ => (hterm W').2
end SemilocLengthSum
end GroundTheory.Heights₂.Heights.Inter
