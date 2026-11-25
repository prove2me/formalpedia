-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.kType_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:52.160104+00:00
-- url     : https://prove2.me/submissions/17648e1f-ebc9-4645-b60a-4b4b75b937e6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKTypeA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PKType
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_alt_comm
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_cntF
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_cntQ
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_colF_lab
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_half
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_isTabF
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_isTabQ
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_pm_mul_alt
import Theorems.Thm_PositivityTheory_Rg_Cz_KTy_sort_data
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
open KTy
namespace PositivityTheory.Rg.Cz
theorem _root_.solution : TensorGl → TransAll → TensorGK → SphAll → Young → KType := by
  intro hGl hTr hGK hSph hY n hn M _ _ ι _ _ Γ _ _ _ _ _ bar κ E ρ hK hG l hl hc ℓ hℓ hW
  obtain ⟨s, w, nu, hnu, hm⟩ := sort_data l hl
  obtain ⟨H, hH⟩ := half bar hK.invol hK.ne
  set lab := lab3 bar (labQ nu) (tl H) with hlab
  have hlabcol : ∀ p q, colF nu H p = colF nu H q → lab p = lab q := fun p q h => colF_lab nu H bar p q h
  have htab := isTabF nu H hm
  let co : Pos nu H → Fin n := fun p => w (lab p) (bF nu H p)
  have hco : ∀ p q, colF nu H p = colF nu H q → co p = co q → p = q := by
    intro p q h h'
    refine htab.1 p q h ?_
    simp only [co, hlabcol p q h] at h'
    exact (w (lab q)).injective h'
  obtain ⟨S, hSA, hS0, hSe⟩ := hTr n M ι E hG.gl hG.comm l hc ℓ hℓ hW (Pos nu H) lab (Col ι n) (colF nu H) (bF nu H)
    co hlabcol htab hco
  have hGK' := hGK n M ι Γ bar κ E ρ hK hG (Pos nu H) lab
  have heig : ∀ τ (u : ℂ), (ℓ ∘ₗ cA (colF nu H) (bF nu H) ∘ₗ S) ∘ₗ qdet (tE (fib lab τ) (E τ)) u =
      ((u + (s : ℂ)) ^ n) • (ℓ ∘ₗ cA (colF nu H) (bF nu H) ∘ₗ S) := by
    intro τ u
    rw [hSe τ u]
    congr 1
    rw [← Fin.prod_const n (u + (s : ℂ))]
    refine Finset.prod_congr rfl fun k _ => ?_
    have e1 : (Finset.univ.filter fun p => lab p = τ ∧ co p = k) =
        Finset.univ.filter fun p => lab p = τ ∧ bF nu H p = (w τ).symm k := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, co]
      constructor
      · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; rw [← h2, h1]; simp
      · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; rw [h2, h1]; simp
    have e2 : (Finset.univ.filter fun p => lab p = τ ∧ bF nu H p = (w τ).symm k).card =
        nu τ ((w τ).symm k) + ((w τ).symm k : ℕ) := cntF nu H bar hK.invol hH τ ((w τ).symm k)
    have e3 := hnu τ ((w τ).symm k)
    rw [Equiv.apply_symm_apply] at e3
    rw [e1, e2]
    have e4 : ((nu τ ((w τ).symm k) + ((w τ).symm k : ℕ) : ℕ) : ℤ) = s - l τ k := by push_cast; linarith
    have e5 : ((nu τ ((w τ).symm k) + ((w τ).symm k : ℕ) : ℕ) : ℂ) = (s : ℂ) - (l τ k : ℂ) := by exact_mod_cast e4
    rw [e5]; ring
  obtain ⟨ξ, hξ, w', hw', hφ⟩ := hSph n hn (TV n M (Pos nu H)) ι Γ bar κ (fun τ => tE (fib lab τ) (E τ))
    (actT lab κ ρ) hK hGK'.1 s _ hS0 heig
  have hcomm : ∀ σ : Equiv.Perm (Pos nu H), (∀ p, lab (σ p) = lab p) →
      ∀ x ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), Commute (pm σ) x := by
    intro σ hσ x hx
    refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx ?_
    rintro _ ⟨τ, a, b, rfl⟩
    exact (hGl n M (Pos nu H) (E τ) (hG.gl τ) (fib lab τ)).2.2.1 σ (by intro p; simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and, hσ]) a b
  have hGc : ∀ σ ∈ colG (colF nu H), ∀ p, lab (σ p) = lab p := by
    intro σ hσ p
    simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    exact hlabcol _ _ (hσ p)
  have hPc : ∀ σ ∈ colG (tl H), ∀ p, lab (dbl (Q := Fin (Fintype.card (Bx nu))) σ p) = lab p := by
    intro σ hσ p
    simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rcases p with p | k | k <;> simp [dbl, hlab, lab3, hσ]
  have hA1 : ∀ x ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), Commute (alt (colG (colF nu H))) x := fun x hx =>
    alt_comm _ _ fun σ hσ => hcomm σ (hGc σ hσ) x hx
  have hA2 : ∀ x ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), Commute (altPair (Q := Fin (Fintype.card (Bx nu))) (tl H)) x := by
    intro x hx
    unfold altPair
    exact Commute.sum_left _ _ _ fun σ hσ => (hcomm _ (hPc σ hσ) x hx).smul_left _
  refine ⟨s, Fintype.card (Bx nu), Fintype.card (Pr H n), labQ nu, colQ nu, bQ nu, tl H,
    alt (colG (colF nu H)) ξ, ?_, isTabQ nu hm, ?_, ?_, ?_, ?_, ?_⟩
  · intro p p' h
    exact hlabcol (.inl p) (.inl p') (by simp [colF, h])
  · intro k k' h
    have h1 := (eP H n k).1.2
    have h2 := (hH (tl H k')).1 (eP H n k').1.2
    exact h2 (by rw [← h]; exact h1)
  · intro τ
    refine ⟨w τ, fun i => ?_⟩
    rw [cntQ, hnu]; ring
  · intro γ
    have := alt_comm (colG (colF nu H)) (actT lab κ ρ γ) fun σ hσ => hGK'.2 σ (hGc σ hσ) γ
    show actT lab κ ρ γ (alt _ ξ) = _
    rw [← Module.End.mul_apply, ← this.eq, Module.End.mul_apply, hξ]
  · intro p p' h hne
    have e := pm_mul_alt (M := M) (n := n) (colG (colF nu H)) (Equiv.swap (Sum.inl p) (Sum.inl p')) ?_
    · rw [← Module.End.mul_apply, e, Equiv.Perm.sign_swap (by simpa using hne)]
      simp
    · intro σ
      simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mul_apply]
      have hs : ∀ x, colF nu H (Equiv.swap (Sum.inl p) (Sum.inl p') x) = colF nu H x := by
        intro x
        rcases eq_or_ne x (.inl p) with rfl | h1
        · simp [colF, h]
        rcases eq_or_ne x (.inl p') with rfl | h2
        · simp [colF, h]
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      simp only [hs]
  · intro h0
    apply hφ
    have e : altPair (tl H) (alt (colG (colF nu H)) (S (w' ξ))) =
        S (w' (altPair (tl H) (alt (colG (colF nu H)) ξ))) := by
      rw [← Module.End.mul_apply (alt _) S, (hA1 S hSA).eq, Module.End.mul_apply,
        ← Module.End.mul_apply (alt _) w', (hA1 w' hw').eq, Module.End.mul_apply,
        ← Module.End.mul_apply (altPair _) S, (hA2 S hSA).eq, Module.End.mul_apply,
        ← Module.End.mul_apply (altPair _) w', (hA2 w' hw').eq, Module.End.mul_apply]
    have hy := hY n M ι (Fin (Fintype.card (Bx nu))) (Fintype.card (Pr H n)) (tl H) (Col ι n) (colF nu H) (bF nu H) htab
      (fun p k => by rcases k with k | k <;> simp [colF]) (fun k k' => by simp [colF])
      (fun k k' => by simp [colF, bF, Prod.ext_iff]) (fun k k' => by simp [colF, bF, Prod.ext_iff])
      (S (w' ξ)) (by rw [e, h0]; simp)
    simp [hy]
end PositivityTheory.Rg.Cz
