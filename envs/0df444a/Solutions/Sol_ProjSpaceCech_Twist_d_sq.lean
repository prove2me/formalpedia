-- Prove2me | solution 1 for ProjSpaceCech.Twist.d_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4aed7d9a-4087-582c-901e-fcc6efa09be5

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ProjSpaceCech_Twist_d_sq

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

universe u

noncomputable section

open Finset Function

namespace ProjSpaceCech
p2m_export "ProjSpaceCech" "Idx.succAbove_comp_succAbove Twist.Mon Twist.Mon.incl Idx Idx.img Idx.face Idx.img_face_subset Twist.faceRes Twist.d Twist.d_apply"
p2m_open "ProjSpaceCech"

section AltCech

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

namespace Twist p2m_export "ProjSpaceCech.Twist" "Mon Mon.incl faceRes d d_apply H" end Twist
p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.d_sq (i : ℕ) :
    Twist.d R n d (i + 1) ∘ₗ Twist.d R n d i = 0 := by
  refine LinearMap.ext fun f => funext fun s => ?_
  rw [LinearMap.comp_apply, Twist.d_apply, LinearMap.zero_apply, Pi.zero_apply]
  simp only [Twist.d_apply, map_sum, map_zsmul, Finset.smul_sum, smul_smul,
    ← pow_add]
  simp only [Twist.faceRes]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  set S : Finset (Fin (i + 3) × Fin (i + 2)) := {ab | (ab.1 : ℕ) ≤ (ab.2 : ℕ)}
  rw [← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_bij
    (fun ab (hab : ab ∈ S) =>
      (ab.2.succ, Fin.castLT ab.1
        (Nat.lt_of_le_of_lt (Finset.mem_filter.mp hab).2 ab.2.isLt)))
    ?hmem ?hinj ?hsurj ?hterm
  case hmem =>
    rintro ⟨a, b⟩ hab
    simp only [S, Finset.compl_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_succ, not_le, Fin.val_castLT]
    exact Nat.lt_succ_of_le (Finset.mem_filter.mp hab).2
  case hinj =>
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    exact Prod.ext (Fin.eq_of_val_eq (by simpa using congrArg Fin.val h2))
      (Fin.succ_injective _ h1)
  case hsurj =>
    rintro ⟨a', b'⟩ hab'
    have hlt : (b' : ℕ) < (a' : ℕ) := by
      simpa [S, Finset.compl_filter, Finset.mem_filter, not_le] using hab'
    have ha'0 : a' ≠ 0 := fun h => by simp [h] at hlt
    refine ⟨(Fin.castSucc b', a'.pred ha'0), ?_, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc,
        Fin.val_pred]; omega
    · exact Prod.ext (Fin.succ_pred a' ha'0)
        (Fin.eq_of_val_eq (by simp only [Fin.val_castLT, Fin.val_castSucc]))
  case hterm =>
    rintro ⟨a, b⟩ hab
    have hba : (a : ℕ) ≤ (b : ℕ) := (Finset.mem_filter.mp hab).2
    set a' : Fin (i + 2) := Fin.castLT a (Nat.lt_of_le_of_lt hba b.isLt)
    have halt : a' ≤ b := Fin.le_def.mpr (by simpa [a'] using hba)
    have hacs : a'.castSucc = a := Fin.eq_of_val_eq (by simp [a'])
    have hface :
        Idx.face n (Idx.face n s a) b
          = Idx.face n (Idx.face n s b.succ) a' := by
      apply Subtype.ext
      change s.1 ∘ (Fin.succAbove a ∘ Fin.succAbove b)
        = s.1 ∘ (Fin.succAbove b.succ ∘ Fin.succAbove a')
      rw [← hacs, Idx.succAbove_comp_succAbove halt]
    have hsign : ((-1 : ℤ) ^ ((a : ℕ) + (b : ℕ)))
        = -((-1 : ℤ) ^ (((b.succ : Fin (i + 3)) : ℕ) + (a' : ℕ))) := by
      simp only [Fin.val_succ, a', Fin.val_castLT]
      rw [show ((b:ℕ) + 1 + (a:ℕ)) = ((a:ℕ) + (b:ℕ)) + 1 from by ring, pow_succ]
      ring
    simp only [Fin.val_succ, a', Fin.val_castLT] at hsign ⊢
    rw [hsign, neg_smul]
    refine congrArg Neg.neg (congrArg₂ (· • ·) rfl ?_)

    have key : ∀ {t t' : Idx n i} (heq : t = t')
        {K K'} (h1 : Idx.img n t ⊆ K) (h1' : K ⊆ Idx.img n s)
        (h2 : Idx.img n t' ⊆ K') (h2' : K' ⊆ Idx.img n s),
        (Finsupp.lmapDomain R R (Twist.Mon.incl n d h1'))
          ((Finsupp.lmapDomain R R (Twist.Mon.incl n d h1)) (f t))
          = (Finsupp.lmapDomain R R (Twist.Mon.incl n d h2'))
            ((Finsupp.lmapDomain R R (Twist.Mon.incl n d h2)) (f t')) := by
      rintro t _ rfl K K' h1 h1' h2 h2'
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Finsupp.lmapDomain_comp,
        ← Finsupp.lmapDomain_comp]
      rfl
    exact key hface (Idx.img_face_subset n _ b)
      (Idx.img_face_subset n s a)
      (Idx.img_face_subset n _ a')
      (Idx.img_face_subset n s b.succ)

end AltCech

end ProjSpaceCech

theorem solution (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (i : ℕ) :
    ProjSpaceCech.Twist.d R n d (i + 1) ∘ₗ ProjSpaceCech.Twist.d R n d i = 0 :=
  ProjSpaceCech.Twist.d_sq R n d i

end

end S_ProjSpaceCech_Twist_d_sq
end P2MW
export P2MW.S_ProjSpaceCech_Twist_d_sq (solution)
