-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_mPiece_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:42:39.065017+00:00
-- url     : https://prove2.me/submissions/833efde7-9e8b-4a13-921f-133020e40327

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ExistsPrimeFiltrationOfIsMultiHomogIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsHomogeneousGrL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_lexDeg_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_mem_grL_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_mHom_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_mem_mHom_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isHomogeneous_grL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_mem_ker_pieceMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_mPiece_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_card_quot_chain
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι} {c : K → ℕ}
    (hf : IsMultiHomog f c) {q : Ideal (MRing ι)} (hq : ∀ g, g ∈ q ↔ g * f ∈ J) {a : K → ℕ}
    (hca : ∀ k, c k ≤ a k) :
    Nat.card (mPiece J a) = Nat.card (mPiece (J ⊔ Ideal.span {f}) a) * Nat.card (mPiece q (a - c)) := by
  classical
  set J' := J ⊔ Ideal.span {f}
  have hJJ' : J ≤ J' := le_sup_left
  set A := LinearMap.ker (pieceMap J a)
  set B := LinearMap.ker (pieceMap J' a)
  have hAB : A ≤ B := fun x hx => by
    rw [mem_ker_pieceMap] at hx ⊢
    exact hJJ' hx
  rw [card_mPiece_eq, card_mPiece_eq, card_mPiece_eq, card_quot_chain A B hAB]
  congr 1
  have hac : a - c + c = a := funext fun k => Nat.sub_add_cancel (hca k)
  have hmul : ∀ g : mHom ι (a - c), (g : MRing ι) * f ∈ mHom ι a := fun g => by
    rw [mem_mHom_iff]
    have := isMultiHomog_mul ((mem_mHom_iff _ _).mp g.2) hf
    rwa [hac] at this
  let χ' : mHom ι (a - c) →ₗ[ℤ] B :=
    { toFun := fun g => ⟨⟨(g : MRing ι) * f, hmul g⟩, by
        rw [mem_ker_pieceMap]
        exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f))⟩
      map_add' := fun g h => by ext; simp [add_mul]
      map_smul' := fun r g => by ext; simp [mul_assoc] }
  let χ := (A.comap B.subtype).mkQ ∘ₗ χ'
  have hsurj : Function.Surjective χ := by
    intro z
    obtain ⟨⟨⟨x, hxa⟩, hxB⟩, rfl⟩ := Submodule.mkQ_surjective _ z
    have hxJ' : x ∈ J' := (mem_ker_pieceMap J' a ⟨x, hxa⟩).mp hxB
    obtain ⟨j, hj, y, hy, hjx⟩ := Submodule.mem_sup.mp hxJ'
    obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    have hf' : f ∈ grL ι (lexDeg c) := (mem_grL_iff f c).mpr hf
    set g := (DirectSum.decompose (grL ι) h (lexDeg (a - c)) : MRing ι)
    have hg : g ∈ mHom ι (a - c) := by
      rw [mHom_eq]
      exact SetLike.coe_mem _
    refine ⟨⟨g, hg⟩, ?_⟩
    have hx : x = (DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) + g * f := by
      have h1 : x ∈ grL ι (lexDeg a) := by rw [← mHom_eq]; exact hxa
      conv_lhs => rw [← DirectSum.decompose_of_mem_same (grL ι) h1, ← hjx]
      rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      congr 1
      rw [← hac, lexDeg_add, DirectSum.coe_decompose_mul_add_of_right_mem (grL ι) hf']
    have hjc : (DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) ∈ J := isHomogeneous_grL hJ _ hj
    show (A.comap B.subtype).mkQ (χ' ⟨g, hg⟩) = (A.comap B.subtype).mkQ ⟨⟨x, hxa⟩, hxB⟩
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap,
      Submodule.coe_subtype, mem_ker_pieceMap]
    have : (((χ' ⟨g, hg⟩ - ⟨⟨x, hxa⟩, hxB⟩ : B) : mHom ι a) : MRing ι) = g * f - x := rfl
    rw [this, hx, show g * f - ((DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) + g * f) =
      -(DirectSum.decompose (grL ι) j (lexDeg a) : MRing ι) by ring]
    exact J.neg_mem hjc
  have hker : LinearMap.ker χ = LinearMap.ker (pieceMap q (a - c)) := by
    ext g
    rw [LinearMap.mem_ker, mem_ker_pieceMap, hq]
    show (A.comap B.subtype).mkQ (χ' g) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
      mem_ker_pieceMap]
    rfl
  rw [← hker]
  exact Nat.card_congr (LinearMap.quotKerEquivOfSurjective χ hsurj).toEquiv.symm
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
