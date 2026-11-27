-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AntisymPerturbation_proof_b0164a6000c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:53:40.959962+00:00
-- url     : https://prove2.me/submissions/637458ea-baab-40d8-9bd4-69deee7108a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PAntisymPerturbation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymPerturbation_rename_mul_eq_or_neg_9d0bf095579c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymPerturbation_rename_swap_eq_or_neg_9ae4b8a333fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AntisymPerturbation_image_comp_perm_eb7e77f1dfa2

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace AntisymPerturbation
theorem _root_.solution (hStab : AntisymStability.Statement) :
    AntisymPerturbation.Statement := by
  intro T _ _ N j hj hjN h K hK
  let jm : Fin N := ⟨j - 1, by omega⟩
  let jp : Fin N := ⟨j, hjN⟩
  let σ : T → Fin N → Fin N → Equiv.Perm (T × Fin N) := fun τ a b =>
    Equiv.swap (τ, a) (τ, jm) * Equiv.swap (τ, b) (τ, jp)
  have hσa : ∀ (τ : T) (a b : Fin N), a.val < j → j ≤ b.val → σ τ a b (τ, a) = (τ, jm) := by
    intro τ a b ha hb
    have e1 : Equiv.swap (τ, b) (τ, jp) (τ, a) = (τ, a) := Equiv.swap_apply_of_ne_of_ne
      (by simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff]; omega)
      (by simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff, jp]; omega)
    simp only [σ, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [e1, Equiv.swap_apply_left]
  have hσb : ∀ (τ : T) (a b : Fin N), a.val < j → j ≤ b.val → σ τ a b (τ, b) = (τ, jp) := by
    intro τ a b ha hb
    simp only [σ, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne
      (by simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff, jp]; omega)
      (by simp only [ne_eq, Prod.mk.injEq, true_and, Fin.ext_iff, jp, jm]; omega)
  have hsign : ∀ R ∈ antisymSpace T N j, ∀ (τ : T) (a b : Fin N), a.val < j → j ≤ b.val →
      rename ⇑(σ τ a b) R = R ∨ rename ⇑(σ τ a b) R = -R := by
    intro R hR τ a b ha hb
    refine AntisymPerturbation.rename_mul_eq_or_neg
      (AntisymPerturbation.rename_swap_eq_or_neg hR τ a jm (by simp only [jm]; omega)
        (Or.inl (by simp only [jm]; omega))) ?_
    rw [Equiv.swap_comm]
    exact AntisymPerturbation.rename_swap_eq_or_neg hR τ jp b (by simp only [jp]; omega)
      (Or.inr (by simp only [jp]; omega))
  obtain ⟨C, hC⟩ := hStab T N j (fun τ a b => (fun y => y ∘ ⇑(σ τ a b)) '' K τ)
    (fun τ a b ha hb => AntisymPerturbation.image_comp_perm (σ τ a b) τ (hσa τ a b ha hb)
      (hσb τ a b ha hb) (hK τ).1 (hK τ).2.1 (hK τ).2.2.1)
  rcases isEmpty_or_nonempty T with hT | ⟨⟨τ0⟩⟩
  · refine ⟨0, fun P v ε hR _ => ?_⟩
    obtain ⟨l, hl, hb⟩ := hC _ hR
    exact ⟨l, hl, fun m => by simpa using hb 0 le_rfl (fun τ => isEmptyElim τ) m⟩
  · refine ⟨C, fun P v ε hR hε => ?_⟩
    obtain ⟨l, hl, hb⟩ := hC _ hR
    refine ⟨l, hl, hb ε ?_ ?_⟩
    · obtain ⟨O, _, ⟨y, hyO, hyH⟩, hOK⟩ := (hK τ0).2.2.1
      exact (abs_nonneg _).trans (hε τ0 y (hOK ⟨hyO, hyH⟩))
    · rintro τ a b ha hb x ⟨y, hy, rfl⟩
      have hyh : eval y h = 0 := (hK τ).2.2.2 y hy
      have hyP := hε τ y hy
      show |eval (y ∘ ⇑(σ τ a b)) (P - v • h)| ≤ ε
      rw [← eval_rename]
      rcases hsign _ hR τ a b ha hb with e | e
      · rw [e]; simpa [hyh] using hyP
      · rw [e, map_neg, abs_neg]; simpa [hyh] using hyP
end AntisymPerturbation
end GroundTheory.Heights₂.Heights
