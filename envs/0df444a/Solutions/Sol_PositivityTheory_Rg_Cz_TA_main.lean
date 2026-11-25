-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TA.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:06:42.6572+00:00
-- url     : https://prove2.me/submissions/2dc06886-3cc3-4db3-848b-71140abb1718

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAllC
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransAll
import Theorems.Thm_P2M_PositivityTheory_Rg_Cz_TA_qdet_map__2871d26b2e36
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_base
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_cA_lift
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_cA_split
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_card_R
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_card_sub
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_cj_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_comm_of_mem_adjoin
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_conj_tensor_entry_base
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_conj_tensor_entry_fibre
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_glRel_map
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_qdet_commute
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_qdet_lift
import Theorems.Thm_PositivityTheory_Rg_Cz_TA_tE_comm_lift
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TA
namespace PositivityTheory.Rg.Cz.TA
theorem _root_.solution (hT : Trans) (N : ℕ) : TAk N := by
  refine Nat.strong_induction_on N ?_
  intro N ih
  intro n M _ _ ι _ _ E hG hC l hl ℓ hℓ hW P _ _ hN lab C _ col b co hcl htab hinj
  rcases isEmpty_or_nonempty P with hP | ⟨⟨p0⟩⟩
  · exact base lab E l hl ℓ hℓ col b co
  obtain ⟨τ0, hp0⟩ : ∃ τ0, lab p0 = τ0 := ⟨_, rfl⟩
  have hcard : Fintype.card {p : P // ¬ lab p = τ0} < N := by
    rw [← hN]
    exact Fintype.card_subtype_lt (p := fun p => ¬ lab p = τ0) (x := p0) (fun h => h hp0)
  obtain ⟨S1, hS1, hne1, hev1⟩ := ih _ hcard n M {τ : ι // τ ≠ τ0} (fun τ => E τ) (fun τ => hG τ)
    (fun τ τ' h => hC τ τ' (fun e => h (Subtype.ext e))) (fun τ => l τ) (fun τ => hl τ) ℓ hℓ
    (fun τ => hW τ) {p : P // ¬ lab p = τ0} rfl (labR lab τ0) C (fun p => col p) (fun p => b p)
    (fun p => co p) (fun p q h => Subtype.ext (hcl p q h))
    ⟨fun p q h1 h2 => Subtype.ext (htab.1 _ _ h1 h2), fun p i hi => by
      obtain ⟨r, hr1, hr2⟩ := htab.2 p i hi
      exact ⟨⟨r, by rw [hcl r p hr1]; exact p.2⟩, hr1, hr2⟩⟩
    (fun p q h1 h2 => Subtype.ext (hinj _ _ h1 h2))
  unfold envAlg at hS1
  have hWh1 : IsWh (fun a c => lift (P := {p : P // ¬ lab p = τ0}) (E τ0 a c))
      (ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) := by
    obtain ⟨ψ, h1, h2, h3⟩ := hW τ0
    refine ⟨ψ, h1, h2, fun a c hac => ?_⟩
    have hcomm : Commute S1 (lift (E τ0 a c)) := comm_of_mem_adjoin hS1 (by
      rintro T ⟨τ, c', d', rfl⟩
      exact tE_comm_lift _ _ _ (fun x y => hC τ τ0 τ.2 x y a c) c' d')
    have e2 := cA_lift (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) (E τ0 a c)
    apply LinearMap.ext
    intro F
    have := LinearMap.congr_fun hcomm.eq F
    have h3' := LinearMap.congr_fun (h3 a c hac)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Module.End.mul_apply] at this h3' ⊢
    rw [this, ← LinearMap.comp_apply (cA _ _) (lift _), e2, LinearMap.comp_apply, h3']
  have hWh1' := hWh1
  obtain ⟨S0, hS0, hne0, hev0⟩ := hT n (TV n M {p : P // ¬ lab p = τ0})
    (fun a c => lift (P := {p : P // ¬ lab p = τ0}) (E τ0 a c))
    (by have := glRel_map (liftA n M {p : P // ¬ lab p = τ0}) (E τ0) (hG τ0); simpa only [liftA_apply] using this)
    (l τ0) (qdet_lift _ _ (hl τ0)) _ hne1 hWh1 {p : P // lab p = τ0} C (fun p => col p) (fun p => b p) (fun p => co p)
    ⟨fun p q h1 h2 => Subtype.ext (htab.1 _ _ h1 h2), fun p i hi => by
      obtain ⟨r, hr1, hr2⟩ := htab.2 p i hi
      exact ⟨⟨r, by rw [hcl r p hr1]; exact p.2⟩, hr1, hr2⟩⟩
    (fun p q h1 h2 => Subtype.ext (hinj _ _ h1 h2))
  unfold envAlg at hS0
  have hcAl : ∀ (B : Module.End ℂ (TV n M {p : P // ¬ lab p = τ0})) (z : TV n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0}),
      cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) (lift B z) = B (cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) z) := fun B z => LinearMap.congr_fun (cA_lift _ _ B) z
  have hkey : ∀ Y : Module.End ℂ (TV n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0}),
      (ℓ ∘ₗ cA col b ∘ₗ cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) (lift (P := {p : P // lab p = τ0}) S1 * S0)) ∘ₗ cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) Y =
        (((ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) ∘ₗ cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) ∘ₗ S0) ∘ₗ Y) ∘ₗ (spl (n := n) (M := M) (fun p : P => lab p = τ0)).toLinearMap := by
    intro Y
    apply LinearMap.ext
    intro F
    simp only [LinearMap.comp_apply, cj_apply, LinearEquiv.apply_symm_apply, Module.End.mul_apply, LinearEquiv.coe_coe]
    rw [cA_split (fun p => lab p = τ0) col (fun p p' h => by rw [hcl p p' h]) b]
    simp only [LinearEquiv.apply_symm_apply, Module.End.mul_apply]
    rw [hcAl]
  have hkey0 : ℓ ∘ₗ cA col b ∘ₗ cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) (lift (P := {p : P // lab p = τ0}) S1 * S0) =
        ((ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) ∘ₗ cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) ∘ₗ S0) ∘ₗ (spl (n := n) (M := M) (fun p : P => lab p = τ0)).toLinearMap := by
    apply LinearMap.ext
    intro F
    simp only [LinearMap.comp_apply, cj_apply, LinearEquiv.apply_symm_apply, Module.End.mul_apply, LinearEquiv.coe_coe]
    rw [cA_split (fun p => lab p = τ0) col (fun p p' h => by rw [hcl p p' h]) b]
    simp only [LinearEquiv.apply_symm_apply, Module.End.mul_apply]
    rw [hcAl]
  refine ⟨cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) (lift (P := {p : P // lab p = τ0}) S1 * S0), ?_, ?_, ?_⟩
  · unfold envAlg
    rw [map_mul]
    apply Subalgebra.mul_mem
    · have hsub : Algebra.adjoin ℂ {T : Module.End ℂ (TV n M {p : P // ¬ lab p = τ0}) | ∃ (τ : {τ : ι // τ ≠ τ0}) (a c : Fin n),
          T = tE (fib (labR lab τ0) τ) (E τ) a c} ≤
          (Algebra.adjoin ℂ {T : Module.End ℂ (TV n M P) | ∃ (τ : ι) (a c : Fin n), T = tE (fib lab τ) (E τ) a c}).comap
            ((cj (spl (n := n) (M := M) (fun p : P => lab p = τ0))).comp (liftA n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0})) := by
        apply Algebra.adjoin_le
        rintro T ⟨τ, c, d, rfl⟩
        simp only [SetLike.mem_coe, Subalgebra.mem_comap, AlgHom.comp_apply, liftA_apply]
        rw [conj_tensor_entry_fibre]
        exact Algebra.subset_adjoin ⟨τ, c, d, rfl⟩
      have := hsub hS1
      simpa only [Subalgebra.mem_comap, AlgHom.comp_apply, liftA_apply] using this
    · have hsub : Algebra.adjoin ℂ {T : Module.End ℂ (TV n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0}) | ∃ (_ : Unit) (a c : Fin n),
          T = tE Finset.univ (fun a c => lift (P := {p : P // ¬ lab p = τ0}) (E τ0 a c)) a c} ≤
          (Algebra.adjoin ℂ {T : Module.End ℂ (TV n M P) | ∃ (τ : ι) (a c : Fin n), T = tE (fib lab τ) (E τ) a c}).comap
            (cj (spl (n := n) (M := M) (fun p : P => lab p = τ0))) := by
        apply Algebra.adjoin_le
        rintro T ⟨_, c, d, rfl⟩
        simp only [SetLike.mem_coe, Subalgebra.mem_comap]
        rw [conj_tensor_entry_base]
        exact Algebra.subset_adjoin ⟨τ0, c, d, rfl⟩
      exact hsub hS0
  · rw [hkey0]
    intro h
    apply hne0
    apply LinearMap.ext
    intro G
    have := LinearMap.congr_fun h ((spl (n := n) (M := M) (fun p : P => lab p = τ0)).symm G)
    simpa using this
  · intro τ u
    by_cases hτ : τ = τ0
    · subst hτ
      have hq : qdet (tE (fib lab τ) (E τ)) u =
          cj (spl (n := n) (M := M) (fun p : P => lab p = τ)) (qdet (tE Finset.univ (fun a c => lift (P := {p : P // ¬ lab p = τ}) (E τ a c))) u) := by
        rw [qdet_map']
        simp only [conj_tensor_entry_base]
      rw [hq, hkey, hev0 u, LinearMap.smul_comp, ← hkey0]
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      congr 2
      exact card_sub (fun p : P => lab p = τ) (fun p => co p = k)
    · have hq : qdet (tE (fib lab τ) (E τ)) u =
          cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) (lift (P := {p : P // lab p = τ0}) (qdet (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u)) := by
        have := qdet_map' ((cj (spl (n := n) (M := M) (fun p : P => lab p = τ0))).comp (liftA n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0})) (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u
        simp only [AlgHom.comp_apply, liftA_apply, conj_tensor_entry_fibre] at this
        exact this.symm
      have hcQ : Commute S0 (lift (P := {p : P // lab p = τ0}) (qdet (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u)) :=
        comm_of_mem_adjoin hS0 (by
          rintro T ⟨_, c, d, rfl⟩
          exact tE_comm_lift _ _ _ (fun x y => (qdet_commute _ u _ (fun a' c' =>
            tE_comm_lift _ _ _ (fun x' y' => hC τ τ0 hτ x' y' x y) a' c')).symm) c d)
      have hmid : (((ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) ∘ₗ cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) ∘ₗ S0) ∘ₗ lift (P := {p : P // lab p = τ0}) (qdet (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u)) =
          ((ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) ∘ₗ qdet (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u) ∘ₗ cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) ∘ₗ S0 := by
        apply LinearMap.ext
        intro F
        have := LinearMap.congr_fun hcQ.eq F
        simp only [LinearMap.comp_apply, Module.End.mul_apply] at this ⊢
        rw [this, hcAl]
      rw [hq, hkey, hmid, hev1 ⟨τ, hτ⟩ u, LinearMap.smul_comp, LinearMap.smul_comp, ← hkey0]
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      rw [card_R]
end PositivityTheory.Rg.Cz.TA
