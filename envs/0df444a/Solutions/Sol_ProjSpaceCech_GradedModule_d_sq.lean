-- Prove2me | solution 1 for ProjSpaceCech.GradedModule.d_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/fee4a904-8fcf-5478-86fb-d08f91985875

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ProjSpaceCech_GradedModule_d_sq

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

universe u

noncomputable section

open Finset Function MvPolynomial

namespace ProjSpaceCech
p2m_export "ProjSpaceCech" "Idx.succAbove_comp_succAbove Idx Idx.img Idx.face Idx.img_face_subset GradedModule GradedModule.secIncl GradedModule.secIncl_trans GradedModule.faceRes GradedModule.d GradedModule.d_apply GradedModule.H"
p2m_open "ProjSpaceCech"

section GradAltdSq

variable {R : Type u} [CommRing R] {n : ℕ}
variable (D : GradedModule R n)

namespace GradedModule p2m_export "ProjSpaceCech.GradedModule" "secIncl secIncl_trans faceRes d d_apply H" end GradedModule
p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.d_sq' (i : ℕ) :
    GradedModule.d D (i + 1) ∘ₗ GradedModule.d D i = 0 := by
  refine LinearMap.ext fun f => funext fun s => ?_
  rw [LinearMap.comp_apply, GradedModule.d_apply, LinearMap.zero_apply, Pi.zero_apply]
  simp only [GradedModule.d_apply, map_sum, map_smul, Finset.smul_sum, smul_smul,
    ← pow_add]
  simp only [GradedModule.faceRes]
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
    have hsign : ((-1 : R) ^ ((a : ℕ) + (b : ℕ)))
        = -((-1 : R) ^ (((b.succ : Fin (i + 3)) : ℕ) + (a' : ℕ))) := by
      simp only [Fin.val_succ, a', Fin.val_castLT]
      rw [show ((b:ℕ) + 1 + (a:ℕ)) = ((a:ℕ) + (b:ℕ)) + 1 from by ring, pow_succ]
      ring
    simp only [Fin.val_succ, a', Fin.val_castLT] at hsign ⊢
    rw [hsign, neg_smul]
    refine congrArg Neg.neg (congrArg₂ (· • ·) rfl ?_)

    have key : ∀ {t t' : Idx n i} (heq : t = t')
        {K K'} (h1 : Idx.img n t ⊆ K) (h1' : K ⊆ Idx.img n s)
        (h2 : Idx.img n t' ⊆ K') (h2' : K' ⊆ Idx.img n s),
        (GradedModule.secIncl D h1') ((GradedModule.secIncl D h1) (f t))
          = (GradedModule.secIncl D h2') ((GradedModule.secIncl D h2) (f t')) := by
      rintro t _ rfl K K' h1 h1' h2 h2'
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
        GradedModule.secIncl_trans, GradedModule.secIncl_trans]
    exact key hface (Idx.img_face_subset n _ b)
      (Idx.img_face_subset n s a)
      (Idx.img_face_subset n _ a')
      (Idx.img_face_subset n s b.succ)

p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.range_d_le_ker (i : ℕ) :
    LinearMap.range (GradedModule.d D i)
      ≤ LinearMap.ker (GradedModule.d D (i + 1)) := by
  rintro _ ⟨f, rfl⟩
  exact LinearMap.congr_fun (GradedModule.d_sq' D i) f

end GradAltdSq

end ProjSpaceCech

theorem solution {R : Type u} [CommRing R] {n : ℕ} (D : ProjSpaceCech.GradedModule R n) (i : ℕ) :
    ProjSpaceCech.GradedModule.d D (i + 1) ∘ₗ ProjSpaceCech.GradedModule.d D i = 0 :=
  ProjSpaceCech.GradedModule.d_sq' D i

end

end S_ProjSpaceCech_GradedModule_d_sq
end P2MW
export P2MW.S_ProjSpaceCech_GradedModule_d_sq (solution)
