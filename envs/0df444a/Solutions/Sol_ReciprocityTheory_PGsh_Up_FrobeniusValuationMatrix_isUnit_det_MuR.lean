-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix.isUnit_det_MuR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:42:56.656571+00:00
-- url     : https://prove2.me/submissions/b0fbed86-86d9-4d30-87b8-7395f6b917b2

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_ProdEraseUpdate
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatementHolds
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_det_map__ae2c7b07d364
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_residue_p
import Theorems.Thm_ReciprocityTheory_PGsh_Up_FrobeniusValuationMatrix_residue_uR
import Theorems.Thm_ReciprocityTheory_PGsh_Up_det_monF_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
open ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
namespace ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
theorem _root_.solution (hv : v.Integers R) (hp1 : v (algebraMap R C (p : R)) < 1)
    (D : Lifts H U X) : IsUnit (MuR hv D).det := by
  haveI : Nontrivial R := (algebraMap R C).domain_nontrivial
  have hlt : ∀ x : R, x ∈ nonunits R → v (algebraMap R C x) < 1 := fun x hx =>
    lt_of_le_of_ne (hv.map_le_one x) fun h => hx (hv.isUnit_iff_valuation_eq_one.mpr h)
  letI : IsLocalRing R := IsLocalRing.of_nonunits_add fun a b ha hb hu => by
    have h1 := hv.isUnit_iff_valuation_eq_one.mp hu
    have h2 : v (algebraMap R C (a + b)) < 1 := by
      rw [map_add]; exact v.map_add_lt (hlt a ha) (hlt b hb)
    rw [h1] at h2
    exact lt_irrefl _ h2
  haveI : CharP (IsLocalRing.ResidueField R) p :=
    (CharP.charP_iff_prime_eq_zero Fact.out).mpr (residue_p hv hp1)
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hM : (IsLocalRing.residue R).mapMatrix (MuR hv D) =
      Matrix.of fun (x α : Nb p g) => monF (p := p) (D.Λ.map (IsLocalRing.residue R)) α x := by
    ext y α
    simp [MuR, monF, residue_uR hv D]
  rw [hM]
  refine det_monF_ne_zero _ ?_
  rw [det_map']
  exact D.Λ_det.map _
end ReciprocityTheory.PGsh.Up.FrobeniusValuationMatrix
