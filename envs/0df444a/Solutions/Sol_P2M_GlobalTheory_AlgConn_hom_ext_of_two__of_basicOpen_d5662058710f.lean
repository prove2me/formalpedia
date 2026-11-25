-- Prove2me | solution 1 for P2M_GlobalTheory_AlgConn_hom_ext_of_two__of_basicOpen_d5662058710f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:05:38.831697+00:00
-- url     : https://prove2.me/submissions/d1a78873-9c58-42f2-adf3-ab6fddbfb337

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClopenBasicOpenSpecProdSelfFirstIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentOfClopen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentEqOfBasicOpenEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomExtSpecProdSelfOfBasicOpenPreimageEq
import Theorems.Thm_P2M_GlobalTheory_AlgConn_hom_eq_toSpec__comp_f14dc953d336
import Theorems.Thm_GlobalTheory_idempotent_eq_of_basicOpen_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AlgConn
namespace GlobalTheory.AlgConn
theorem _root_.solution : ∀ (O : Type) [CommRing O] (T : Scheme.{0})
    (h h' : T ⟶ Spec (.of (O × O))), h ≫ twoπ O = h' ≫ twoπ O →
    h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) = h' ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) →
    h = h' := by
  intro O _ T h h' hπ hb
  rw [hom_eq_toSpecΓ_comp h, hom_eq_toSpecΓ_comp h']
  congr 2

  have h1 : ∀ a : O, ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h.appTop).hom (algebraMap O (O × O) a) =
      ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h'.appTop).hom (algebraMap O (O × O) a) := by
    intro a
    have key : ∀ g : T ⟶ Spec (.of (O × O)),
        ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ g.appTop).hom (algebraMap O (O × O) a) =
          ((Scheme.ΓSpecIso (.of O)).inv ≫ (g ≫ twoπ O).appTop).hom a := by
      intro g
      rw [Scheme.Hom.comp_appTop, ← Category.assoc]
      have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap O (O × O)))
      have n' : CommRingCat.ofHom (algebraMap O (O × O)) ≫ (Scheme.ΓSpecIso (.of (O × O))).inv =
          (Scheme.ΓSpecIso (.of O)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap O (O × O)))).appTop := by
        rw [Iso.eq_inv_comp, ← Category.assoc, ← n, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [← n']
      rfl
    rw [key h, key h', hπ]

  have h2 : ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h.appTop).hom ((1, 0) : O × O) =
      ((Scheme.ΓSpecIso (.of (O × O))).inv ≫ h'.appTop).hom ((1, 0) : O × O) := by
    change h.appTop (fst1 O) = h'.appTop (fst1 O)
    have hid : fst1 O * fst1 O = fst1 O := by
      rw [fst1, ← map_mul]; congr 1; ext <;> simp
    apply GlobalTheory.idempotent_eq_of_basicOpen_eq T
    · rw [← map_mul, hid]
    · rw [← map_mul, hid]
    · rw [← Scheme.preimage_basicOpen_top, ← Scheme.preimage_basicOpen_top, hb]

  ext1
  ext x
  obtain ⟨a, b⟩ := x
  have hx : ((a, b) : O × O) = algebraMap O (O × O) a * (1, 0) + algebraMap O (O × O) b * (1 - (1, 0)) := by
    ext <;> simp
  rw [hx, map_add, map_mul, map_mul, map_sub, map_one, map_add, map_mul, map_mul, map_sub, map_one, h1 a, h1 b, h2]
end GlobalTheory.AlgConn
