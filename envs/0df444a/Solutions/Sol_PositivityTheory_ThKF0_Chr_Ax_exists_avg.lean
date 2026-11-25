-- Prove2me | solution 1 for PositivityTheory.ThKF0.Chr.Ax.exists_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:23.466863+00:00
-- url     : https://prove2.me/submissions/f6698e8d-2aab-4950-8676-c8ed411310c6

import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_SchrodingerApplyZeroOfFst
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_CharacterAdmissibility_BoxCancel
import Theorems.Thm_PositivityTheory_ThKF0_Chr_rel_dv
import Theorems.Thm_PositivityTheory_ThKF0_Chr_kE_dv
import Theorems.Thm_PositivityTheory_ThKF0_Chr_isSp_fE
import Theorems.Thm_PositivityTheory_ThKF0_Chr_isSp_kE
import Theorems.Thm_P2M_PositivityTheory_ThKF0_Chr_extend_zero__0eec8e0f4aea
import Theorems.Thm_PositivityTheory_ThKF0_Chr_AxImp_ex
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_comp_ne
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_cyc
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_isE_res
import Theorems.Thm_PositivityTheory_ThKF0_Chr_Ax_line
import Theorems.Thm_PositivityTheory_ThKF0_Chr_IsImp_cyc
import Theorems.Thm_PositivityTheory_ThKF0_Chr_IsSp_trans
import Theorems.Thm_PositivityTheory_ThKF0_Chr_schrodinger_translate_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Chr
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {κ κ₁ : Type}
variable [Fintype κ] [Fintype κ₁]
variable [Invertible (2 : R)] {C : TestClass R} {ψ : AddChar R ℂ}
variable {S : V R κ ≃ₗ[R] V R κ} {j : κ₁ → κ} {e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)}
  {E : ((κ ⊕ κ → R) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ₁ → R) → ℂ)}
namespace PositivityTheory.ThKF0.Chr
namespace Ax
theorem _root_.solution (h : Ax C ψ) (hI : AxInt C) (hS : IsSp S) (hj : Function.Injective j)
    (hE : IsE C ψ (dbS S) (Sum.map j j) E) {l : ((κ₁ ⊕ κ₁ → R) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ C.adm (κ₁ ⊕ κ₁))
    (hinv : ∀ w : V R κ₁, ∀ φ ∈ C.sp (κ₁ ⊕ κ₁), l (schr ψ (dv w w) φ) = l φ) (hc : Cyc C ψ l)
    (ρ : Type) [Fintype ρ] (i : ρ → κ) (hi : Function.Injective i) (hij : ∀ k, (∃ a, i a = k) ↔ ¬ ∃ a, j a = k) :
    ∃ L ∈ C.adm (κ ⊕ κ), (∃ φ ∈ C.sp (κ ⊕ κ), L φ ≠ 0) ∧ (∀ w : V R κ, ∀ φ ∈ C.sp (κ ⊕ κ), L (schr ψ (dv w w) φ) = L φ) ∧
      ∀ (O : Module.End ℂ ((κ ⊕ κ → R) → ℂ)) (a : ℂ) (g : (ρ → R) ≃ₗ[R] (ρ → R)), a ≠ 0 → (∀ φ ∈ C.sp (κ ⊕ κ), O φ ∈ C.sp (κ ⊕ κ)) →
        (∀ u, ∀ φ ∈ C.sp (κ ⊕ κ), O (schr ψ (dv (S.symm (Function.extend i u 0, 0)) (S.symm (Function.extend i u 0, 0))) φ) =
          schr ψ (dv (S.symm (Function.extend i (g u) 0, 0)) (S.symm (Function.extend i (g u) 0, 0))) (O φ)) →
        (∀ φ ∈ C.sp (κ ⊕ κ), l (E (O φ)) = a * l (E φ)) →
        ∀ φ ∈ C.sp (κ ⊕ κ), L (O φ) = a * ((C.modu (LinearEquiv.det g) : ℝ) : ℂ) * L φ := by
  classical
  set K := (dbS S).trans (kE R fun k => ∃ a, j a = k) with hK
  have hKs : IsSp K := hS.dbS.trans (isSp_kE _)
  have hKd : ∀ w w', K (dv w w') = kE R (fun k => ∃ a, j a = k) (dv (S w) (S w')) := fun w w' => by
    rw [hK, LinearEquiv.trans_apply, dbS_dv]
  obtain ⟨T, hT⟩ := h.imp.ex hKs
  have hi' : Function.Injective (Sum.inr ∘ i : ρ → κ ⊕ κ) := Sum.inr_injective.comp hi
  have hE' := h.isE_res hT hi'
  obtain ⟨I, hIa, hIne, hIt, hIg⟩ := hI ρ
  have hIc : Cyc C ψ I := h.cyc isSp_fE hIa (fun w hw φ hφ => by
    rw [show w = (w.1, 0) from Prod.ext rfl hw, schrodinger_translate_apply, hIt _ _ hφ]) hIne
  have hx : ∀ u : ρ → R, Function.extend (Sum.inr ∘ i : ρ → κ ⊕ κ) u 0 = Sum.elim (0 : κ → R) (Function.extend i u 0) := fun u => by
    funext k
    rcases k with k | k
    · rw [Function.extend_apply' _ _ _ (by simp)]; rfl
    · by_cases hk : ∃ a, i a = k
      · obtain ⟨a, rfl⟩ := hk
        rw [Sum.elim_inr, hi.extend_apply]
        exact hi'.extend_apply _ _ a
      · rw [Sum.elim_inr, Function.extend_apply' _ _ _ hk, Function.extend_apply' _ _ _ (by simpa using hk)]; rfl
  have hrel : ∀ w : V R κ, Rel K (Sum.inr ∘ i) (dv w w) ((S w).1 ∘ i, 0) := fun w => by
    rw [Rel, hKd, kE_dv, hx]
    refine ⟨funext fun k => ?_, funext fun a => ?_⟩
    · rcases k with k | k
      · simp
      · by_cases hk : ∃ a, i a = k
        · have := (hij k).1 hk
          obtain ⟨a, rfl⟩ := hk
          simp only [Sum.elim_inr, if_neg this, hi.extend_apply, Function.comp_apply]
        · simp only [Sum.elim_inr, if_pos (not_not.1 (mt (hij k).2 hk)), Function.extend_apply' _ _ _ hk, sub_self, Pi.zero_apply]
    · simp only [Function.comp_apply, Sum.elim_inr, if_neg ((hij _).1 ⟨a, rfl⟩), sub_self, Pi.zero_apply]
  obtain ⟨c, hc'⟩ := h.line hKs hT (hE.adm l hl) fun w hw φ hφ => by
    obtain ⟨a, b, rfl⟩ := exists_dv w
    rw [hKd, kE_dv] at hw
    have h1 : (S a).1 = (S b).1 := funext fun k => sub_eq_zero.1 (congrFun hw (.inl k))
    have h2 : (S b).1 = Function.extend j ((S b).1 ∘ j) 0 := funext fun k => by
      by_cases hk : ∃ a, j a = k
      · obtain ⟨a, rfl⟩ := hk
        rw [hj.extend_apply]; rfl
      · rw [Function.extend_apply' _ _ _ hk]
        simpa [hk] using congrFun hw (.inr k)
    have h3 : (S a).2 ∘ j = (S b).2 ∘ j := funext fun k => by
      have := congrFun hw (.inr (j k))
      simp only [Sum.elim_inr, if_pos (⟨k, rfl⟩ : ∃ a, j a = j k), Pi.zero_apply] at this
      exact sub_eq_zero.1 this
    show l (E _) = l (E φ)
    rw [hE.law _ _ ((rel_dv hj (w₁ := ((S b).1 ∘ j, (S b).2 ∘ j)) (w₁' := ((S b).1 ∘ j, (S b).2 ∘ j))).2
      ⟨⟨h1.trans h2, h3⟩, ⟨h2, rfl⟩⟩) φ hφ, hinv _ _ (hE.maps φ hφ)]
  have hc0 : c ≠ 0 := fun e0 => by
    obtain ⟨φ, hφ, hne⟩ := h.comp_ne hS.dbS (hj.sumMap hj) hE hc
    exact hne ((hc' φ hφ).trans (by rw [e0, zero_mul]))
  have hF : ∀ u, ∀ φ ∈ C.sp (κ ⊕ κ), c * (Chr.res R (Sum.inr ∘ i) ∘ₗ T) φ u =
      l (E (schr ψ (dv (S.symm (Function.extend i u 0, 0)) (S.symm (Function.extend i u 0, 0))) φ)) := fun u φ hφ => by
    refine Eq.trans ?_ (hc' _ (h.schr _ _ _ hφ)).symm
    have e1 := congrFun (hE'.law _ _ (hrel (S.symm (Function.extend i u 0, 0))) φ hφ) 0
    rw [S.apply_symm_apply, Function.extend_comp hi, schrodinger_translate_apply] at e1
    simp only [zero_add] at e1
    rw [← e1, LinearMap.comp_apply, Chr.res, LinearMap.funLeft_apply, extend_zero' hi']
  refine ⟨I ∘ₗ Chr.res R (Sum.inr ∘ i) ∘ₗ T, hE'.adm I hIa, h.comp_ne hKs hi' hE' hIc, fun w φ hφ => ?_,
    fun O a g ha hO hOl hOa φ hφ => ?_⟩
  · show I ((Chr.res R (Sum.inr ∘ i) ∘ₗ T) _) = I ((Chr.res R (Sum.inr ∘ i) ∘ₗ T) φ)
    rw [hE'.law _ _ (hrel w) φ hφ, schrodinger_translate_apply, hIt _ _ (hE'.maps φ hφ)]
  · have e1 : (Chr.res R (Sum.inr ∘ i) ∘ₗ T) (O φ) = a • fun u => (Chr.res R (Sum.inr ∘ i) ∘ₗ T) φ (g.symm u) := by
      funext u
      refine mul_left_cancel₀ hc0 ?_
      rw [hF _ _ (hO φ hφ), Pi.smul_apply, smul_eq_mul, mul_left_comm, hF _ _ hφ, ← hOa _ (h.schr _ _ _ hφ), hOl _ _ hφ,
        g.apply_symm_apply]
    have m1 : (fun u => (Chr.res R (Sum.inr ∘ i) ∘ₗ T) φ (g.symm u)) ∈ C.sp ρ := by
      have := (C.sp ρ).smul_mem a⁻¹ (hE'.maps _ (hO φ hφ))
      rwa [e1, smul_smul, inv_mul_cancel₀ ha, one_smul] at this
    show I ((Chr.res R (Sum.inr ∘ i) ∘ₗ T) _) = _ * I ((Chr.res R (Sum.inr ∘ i) ∘ₗ T) φ)
    rw [e1, map_smul, hIg g _ (hE'.maps φ hφ) m1, smul_eq_mul, mul_assoc]
end Ax
end PositivityTheory.ThKF0.Chr
