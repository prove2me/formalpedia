-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CtrX.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:59:56.763795+00:00
-- url     : https://prove2.me/submissions/9e5dd5e7-f1a1-45e1-9767-6e1cabf3621d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractD
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractE
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractB
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_prod_update_zpow
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_det_ne
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_actT_Om
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_actT_anti_id
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_actT_reIx
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_actT_unc
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_anti_span
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_cur_anti
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_pm_alt_firstG
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_reIx_smul
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_unc_cur
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_unc_inj
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_unc_smul
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.CtrX
theorem _root_.solution (hQ : QdetFacts) (hW : WallAlg) (hT : TensorGK) (hL : LieInv)
    {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
    {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} {E : ι → Fin n → Fin n → Module.End ℂ M}
    {ρ : Γ → Module.End ℂ M} (hK : IsKD bar κ) (hG : IsGK bar κ E ρ) (τ0 : ι)
    {M0 : Type} [AddCommGroup M0] [Module ℂ M0] (q : M →ₗ[ℂ] M0) (F1 F2 : Fin n → Fin n → Module.End ℂ M0)
    (s : ℂ) (hF1 : GlRel F1) (hF2 : GlRel F2) (hc : ∀ a b c d, Commute (F1 a b) (F2 c d))
    (hs1 : HasChar F1 fun _ => s) (hs2 : HasChar F2 fun _ => s)
    (hq1 : ∀ a b, q ∘ₗ E τ0 a b = F1 a b ∘ₗ q) (hq2 : ∀ a b, q ∘ₗ E (bar τ0) a b = F2 a b ∘ₗ q)
    (hn : 1 ≤ n) (m : ℕ) (hm : 0 < m) (c : ι → ℤ) (ζ : TV n M (Fin m))
    (hζ : ∀ γ, actT (fun _ : Fin m => τ0) κ ρ γ ζ = (∏ τ, (κ τ γ).det ^ c τ) • ζ) (hz : ∃ I, q (ζ I) ≠ 0) :
    ∃ m2 < m, ∃ ζ2 : TV n M (Fin m2), (∀ γ, actT (fun _ : Fin m2 => τ0) κ ρ γ ζ2 =
      (∏ τ, (κ τ γ).det ^ (Function.update c τ0 (c τ0 - 1)) τ) • ζ2) ∧ ∃ I, q (ζ2 I) ≠ 0 := by
  classical
  obtain ⟨hGK, hcomm⟩ := hT n M ι Γ bar κ E ρ hK hG (Fin m) (fun _ => τ0)
  let χ : Γ → ℂ := fun γ => ∏ τ, (κ τ γ).det ^ c τ
  let Y : Submodule ℂ (TV n M (Fin m)) := semiS m τ0 κ ρ c
  have hY : ∀ y, y ∈ Y ↔ ∀ γ, actT (fun _ : Fin m => τ0) κ ρ γ y = χ γ • y := fun y => Iff.rfl
  let Q : TV n M (Fin m) →ₗ[ℂ] TV n M0 (Fin m) := LinearMap.compLeft q (Fin m → Fin n)
  have hQap : ∀ y I, Q y I = q (y I) := fun _ _ => rfl
  have hpmY : ∀ σ : Equiv.Perm (Fin m), ∀ y ∈ Y, pm σ y ∈ Y := by
    intro σ y hy
    rw [hY] at hy ⊢
    intro γ
    have h := congrArg (fun T : Module.End ℂ (TV n M (Fin m)) => T y) (hcomm σ (fun _ => rfl) γ).eq
    simp only [Module.End.mul_apply] at h
    rw [← h, hy γ, map_smul]
  have hOmY : ∀ j : Fin m, ∀ y ∈ Y, Om (E τ0) j y ∈ Y := by
    intro j y hy
    rw [hY] at hy ⊢
    intro γ
    rw [actT_Om τ0 κ (E τ0) ρ γ (hK.unit τ0 γ) (hG.ad γ τ0) j y, hy γ, map_smul]
  have hQpm : ∀ (σ : Equiv.Perm (Fin m)) y, Q (pm σ y) = pm σ (Q y) := by
    intro σ y
    funext I
    rfl
  have hQlift : ∀ (B : Module.End ℂ M) (B' : Module.End ℂ M0), q ∘ₗ B = B' ∘ₗ q → ∀ y, Q (lift B y) = lift B' (Q y) := by
    intro B B' hB y
    funext I
    simp only [hQap, lift, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    exact LinearMap.congr_fun hB (y I)
  have hQeAt : ∀ (p : Fin m) (a b : Fin n) y, Q (eAt p a b y) = eAt p a b (Q y) := by
    intro p a b y
    funext I
    simp only [hQap, eAt, LinearMap.pi_apply]
    split_ifs <;> simp [hQap]
  have hQOm : ∀ (j : Fin m) y, Q (Om (E τ0) j y) = Om F1 j (Q y) := by
    intro j y
    simp only [Om, LinearMap.sum_apply, map_sum, Module.End.mul_apply, hQeAt]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hQlift _ _ (hq1 a b), hQeAt]
  have hfib1 : fib (fun _ : Fin m => τ0) τ0 = Finset.univ := by
    ext p
    simp [fib]
  have hfib2 : fib (fun _ : Fin m => τ0) (bar τ0) = ∅ := by
    ext p
    simp [fib, (hK.ne τ0).symm]
  let c' : ℂ := ((c τ0 - c (bar τ0) : ℤ) : ℂ)
  have hQtE : ∀ y ∈ Y, ∀ a b : Fin n, tE Finset.univ (fun a b => F1 a b + -F2 b a) a b (Q y) = if a = b then c' • Q y else 0 := by
    intro y hy a b
    have h := hL n (TV n M (Fin m)) ι Γ bar κ (fun τ => tE (fib (fun _ : Fin m => τ0) τ) (E τ)) (actT (fun _ : Fin m => τ0) κ ρ) hK hGK c y ((hY y).1 hy) τ0 a b
    simp only [hfib1, hfib2, tE, Finset.sum_empty, add_zero] at h
    have h' := congrArg Q h
    rw [map_sub, LinearMap.add_apply, map_add, LinearMap.sum_apply, map_sum, hQlift _ _ (hq1 a b), hQlift _ _ (hq2 b a)] at h'
    simp only [hQeAt] at h'
    have hl : ∀ (B1 B2 : Module.End ℂ M0) (v : TV n M0 (Fin m)), lift (B1 + -B2) v = lift B1 v - lift B2 v := by
      intro B1 B2 v
      funext I
      simp [lift, sub_eq_add_neg]
    simp only [tE, LinearMap.add_apply, hl, LinearMap.sum_apply]
    rw [sub_add_eq_add_sub, h']
    split_ifs <;> simp [c']
  let X : Submodule ℂ (TV n M0 (Fin m)) := Y.map Q
  have hζY : ζ ∈ Y := (hY ζ).2 hζ
  have hXne : X ≠ ⊥ := by
    obtain ⟨I, hI⟩ := hz
    intro hX
    have hmem : Q ζ ∈ X := Submodule.mem_map_of_mem hζY
    rw [hX, Submodule.mem_bot] at hmem
    exact hI (by rw [← hQap, hmem]; rfl)
  have hXpm : ∀ σ : Equiv.Perm (Fin m), ∀ ξ ∈ X, pm σ ξ ∈ X := by
    intro σ ξ hξ
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hξ
    rw [← hQpm]
    exact Submodule.mem_map_of_mem (hpmY σ y hy)
  have hXOm : ∀ j : Fin m, ∀ ξ ∈ X, Om F1 j ξ ∈ X := by
    intro j ξ hξ
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hξ
    rw [← hQOm]
    exact Submodule.mem_map_of_mem (hOmY j y hy)
  have hXtE : ∀ a b : Fin n, ∀ ξ ∈ X, tE Finset.univ (fun a b => F1 a b + -F2 b a) a b ξ = if a = b then c' • ξ else 0 := by
    intro a b ξ hξ
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hξ
    exact hQtE y hy a b
  obtain ⟨-, -, -, hgl2, hch2⟩ := hQ n M0 F2 hF2
  have hcomm12 : ∀ a b c d : Fin n, Commute (F1 a b) (-F2 d c) := fun a b c d => (hc a b d c).neg_right
  obtain ⟨-, hwall⟩ := hW n M0 F1 (fun a b => -F2 b a) hF1 hgl2 hcomm12 s (-((n : ℂ) - 1) - s) c' hs1 (hch2 _ hs2) m X hXne hXpm hXOm hXtE
  obtain ⟨hnm, ξ, hξX, hξalt⟩ := hwall hm
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hξX
  have hQalt : Q (alt (firstG m n) y) = alt (firstG m n) (Q y) := by
    simp only [alt, LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul, hQpm]
  let ζ' : TV n M (Fin m) := alt (firstG m n) y
  have hζ'Y : ζ' ∈ Y := by
    show (∑ σ ∈ firstG m n, ((Equiv.Perm.sign σ : ℤ) : ℂ) • pm σ) y ∈ Y
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem _ (fun σ _ => Submodule.smul_mem _ _ (hpmY σ y hy))
  have hanti : ∀ τ ∈ firstG m n, pm τ ζ' = ((Equiv.Perm.sign τ : ℤ) : ℂ) • ζ' := fun τ hτ => pm_alt_firstG τ hτ y
  have hnz : ∃ I, q (ζ' I) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hξalt
    rw [← hQalt]
    funext I
    rw [hQap]
    exact hcon I
  set e := splitE m n hnm with he
  let g : TV n M (Fin (m - n) ⊕ Fin n) := reIx e ζ'
  let F : TV n (TV n M (Fin (m - n))) (Fin n) := cur g
  have hFanti : ∀ σ : Equiv.Perm (Fin n), pm σ F = ((Equiv.Perm.sign σ : ℤ) : ℂ) • F := cur_anti hnm ζ' hanti
  refine ⟨m - n, by omega, F id, fun γ => ?_, ?_⟩
  · have h1 : actT (fun _ : Fin (m - n) ⊕ Fin n => τ0) κ ρ γ g = χ γ • g := by
      have h0 := actT_reIx e (fun _ : Fin m => τ0) κ ρ γ ζ'
      rw [(hY ζ').1 hζ'Y γ, reIx_smul] at h0
      exact h0
    have h2 : (fun _ : Fin (m - n) ⊕ Fin n => τ0) = Sum.elim (fun _ : Fin (m - n) => τ0) (fun _ : Fin n => τ0) := by
      funext x
      cases x <;> rfl
    have h3 : actT (fun _ : Fin n => τ0) κ (actT (fun _ : Fin (m - n) => τ0) κ ρ) γ F = χ γ • F := by
      apply unc_inj
      rw [← actT_unc, unc_smul, unc_cur, ← h2, h1]
    have h4 := actT_anti_id τ0 κ (actT (fun _ : Fin (m - n) => τ0) κ ρ) γ F hFanti
    rw [h3] at h4
    have hdet := det_ne hK τ0 γ
    rw [prod_update_zpow (fun τ => (κ τ γ).det) c τ0 hdet, mul_smul]
    have h5 := congrArg (fun v => ((κ τ0 γ).det)⁻¹ • v) h4
    simp only [smul_smul, inv_mul_cancel₀ hdet, one_smul, Pi.smul_apply] at h5
    rw [← h5, smul_smul]
  · obtain ⟨I, hI⟩ := hnz
    let K : Fin (m - n) → Fin n := fun k => I (e.symm (Sum.inl k))
    let J : Fin n → Fin n := fun j => I (e.symm (Sum.inr j))
    obtain ⟨a, ha⟩ := anti_span F hFanti J
    refine ⟨K, fun hK0 => hI ?_⟩
    have hIe : Sum.elim K J ∘ e = I := by
      funext x
      simp only [Function.comp_apply]
      generalize hy : e x = w
      cases w with
      | inl k =>
        show I (e.symm (Sum.inl k)) = I x
        rw [← hy, Equiv.symm_apply_apply]
      | inr k =>
        show I (e.symm (Sum.inr k)) = I x
        rw [← hy, Equiv.symm_apply_apply]
    have h6 : ζ' I = F J K := by
      show ζ' I = ζ' (Sum.elim K J ∘ e)
      rw [hIe]
    rw [h6, ha, Pi.smul_apply, map_smul, hK0, smul_zero]
end PositivityTheory.Rg.Cz.CtrX
