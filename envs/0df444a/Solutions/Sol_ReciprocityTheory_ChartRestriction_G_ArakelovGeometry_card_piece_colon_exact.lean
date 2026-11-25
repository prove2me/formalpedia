-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.card_piece_colon_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:12:08.546526+00:00
-- url     : https://prove2.me/submissions/f4489e0d-5009-440c-a695-955db4b193c4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_EqSumMultihomogeneousComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_mem_multidegree_piece_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_quotient_mk_mul_congr_colon
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_mul__08bacea3b256
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_i2comp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_i2comp_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_i2comp_mul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_i2comp_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isMultiHomog_i2comp


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
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {F q : Ideal (MRing ι)} (hF : IsMultiHomogIdeal F) {f : MRing ι} {c : K → ℕ}
    (hf : IsMultiHomog f c) (hq : ∀ g, g ∈ q ↔ g * f ∈ F) {a : K → ℕ} (hca : c ≤ a) :
    Nat.card (mPiece F a) =
      Nat.card (mPiece q (a - c)) * Nat.card (mPiece (F ⊔ Ideal.span {f}) a) := by
  have hle : F ≤ F ⊔ Ideal.span {f} := le_sup_left
  let ψ : mPiece F a →+ MRing ι ⧸ (F ⊔ Ideal.span {f}) :=
    (Ideal.Quotient.factor hle).toAddMonoidHom.comp (mPiece F a).subtype.toAddMonoidHom
  have hψ : ∀ y : mPiece F a, ψ y = Ideal.Quotient.factor hle y.1 := fun _ => rfl
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker
  have h2 : Nat.card (mPiece F a ⧸ ψ.ker) = Nat.card (mPiece (F ⊔ Ideal.span {f}) a) := by
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    rw [AddMonoidHom.mem_range, mem_multidegree_piece_iff]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨h, hh, hx⟩ := mem_multidegree_piece_iff.1 x.2
      refine ⟨h, hh, ?_⟩
      rw [hψ, ← hx, Ideal.Quotient.factor_mk]
    · rintro ⟨h, hh, rfl⟩
      refine ⟨⟨Ideal.Quotient.mk F h, mem_multidegree_piece_iff.2 ⟨h, hh, rfl⟩⟩, ?_⟩
      rw [hψ, Ideal.Quotient.factor_mk]
  have h3 : Nat.card (mPiece q (a - c)) = Nat.card ψ.ker := by
    let g₀ : MRing ι ⧸ q → MRing ι := fun x => (Ideal.Quotient.mk_surjective x).choose
    have hg₀ : ∀ x, Ideal.Quotient.mk q (g₀ x) = x := fun x =>
      (Ideal.Quotient.mk_surjective x).choose_spec
    have hmem1 : ∀ x : mPiece q (a - c), Ideal.Quotient.mk F (g₀ x.1 * f) ∈ mPiece F a := by
      intro x
      obtain ⟨g, hg, hgx⟩ := mem_multidegree_piece_iff.1 x.2
      refine mem_multidegree_piece_iff.2 ⟨g * f, ?_, quotient_mk_mul_congr_colon hq (by rw [hg₀, hgx])⟩
      have := isMultiHomog_mul' hg hf
      rwa [tsub_add_cancel_of_le hca] at this
    have hmem2 : ∀ x : mPiece q (a - c), (⟨_, hmem1 x⟩ : mPiece F a) ∈ ψ.ker := by
      intro x
      rw [AddMonoidHom.mem_ker, hψ]
      show Ideal.Quotient.factor hle (Ideal.Quotient.mk F (g₀ x.1 * f)) = 0
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f))
    refine Nat.card_eq_of_bijective (fun x => ⟨⟨_, hmem1 x⟩, hmem2 x⟩)
      ⟨fun x y hxy => ?_, fun z => ?_⟩
    · have e : Ideal.Quotient.mk F (g₀ x.1 * f) = Ideal.Quotient.mk F (g₀ y.1 * f) :=
        congrArg (fun z : ψ.ker => (z.1.1 : MRing ι ⧸ F)) hxy
      rw [Ideal.Quotient.eq, ← sub_mul, ← hq] at e
      apply Subtype.ext
      rw [← hg₀ x.1, ← hg₀ y.1]
      exact Ideal.Quotient.eq.2 e
    · obtain ⟨⟨y, hy⟩, hz⟩ := z
      obtain ⟨h, hh, rfl⟩ := mem_multidegree_piece_iff.1 hy
      rw [AddMonoidHom.mem_ker, hψ] at hz
      change Ideal.Quotient.factor hle (Ideal.Quotient.mk F h) = 0 at hz
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_sup] at hz
      obtain ⟨u, hu, v, hv, huv⟩ := hz
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hv
      have hx : Ideal.Quotient.mk q (i2comp (a - c) g) ∈ mPiece q (a - c) :=
        mem_multidegree_piece_iff.2 ⟨_, isMultiHomog_i2comp _ _, rfl⟩
      refine ⟨⟨_, hx⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      show Ideal.Quotient.mk F (g₀ (Ideal.Quotient.mk q (i2comp (a - c) g)) * f) =
        Ideal.Quotient.mk F h
      rw [quotient_mk_mul_congr_colon hq (hg₀ _)]
      have e : h = i2comp a u + i2comp (a - c) g * f := by
        rw [← i2comp_self hh, ← huv, i2comp_add, i2comp_mul_right hf, if_pos hca]
      rw [e, Ideal.Quotient.eq]
      have e2 : i2comp (a - c) g * f - (i2comp a u + i2comp (a - c) g * f) = -i2comp a u := by ring
      rw [e2]
      exact neg_mem (i2comp_mem hF a hu)
  rw [h1, h2, ← h3, mul_comm]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
