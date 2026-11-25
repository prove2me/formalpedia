-- Prove2me | solution 1 for PositivityTheory.ThKR.Join.tens_join
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:39:03.636553+00:00
-- url     : https://prove2.me/submissions/c6a74a2a-3a6f-439c-8453-aa028f67a3d6

import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_TensMax
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_TensJoin
import Theorems.Thm_PositivityTheory_ThKR_Join_map_st
import Theorems.Thm_PositivityTheory_ThKF_Unit_ker_le
import Theorems.Thm_PositivityTheory_ThKF_Unit_tens_max


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open PiTensorProduct
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.Join
open PositivityTheory.ThKF.Unit
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
namespace PositivityTheory.ThKR.Join
theorem _root_.solution {A : ι → Type} (act : ∀ i, A i → Module.End ℂ (V i)) (K Z : ∀ i, Submodule ℂ (V i))
    (hr : ∀ i, Module.rank ℂ (V i) ≤ Cardinal.aleph0) (h1 : ∀ i, K i ≠ ⊤) (h2 : ∀ i a, ∀ x ∈ K i, act i a x ∈ K i)
    (h3 : ∀ i N, K i ≤ N → (∀ a, ∀ x ∈ N, act i a x ∈ N) → N = K i ∨ N = ⊤) (v : ∀ i, V i)
    (h4 : ∀ i (t : List (V i)), (∀ x ∈ t, x ∈ K i) → ∀ y,
      ∃ u ∈ Algebra.adjoin ℂ (Set.range (act i)), u (v i) - y ∈ Z i ∧ ∀ x ∈ t, u x ∈ Z i)
    (P P' : Submodule ℂ (⨂[ℂ] i, V i)) (hZ : ∀ (f : ∀ i, V i) i, f i ∈ Z i → tprod ℂ f ∈ P)
    (hZ' : ∀ (f : ∀ i, V i) i, f i ∈ Z i → tprod ℂ f ∈ P')
    (hP : ∀ i a, ∀ x ∈ P, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P)
    (hP' : ∀ i a, ∀ x ∈ P', map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ P')
    (e : P ⊔ P' = ⊤) : P = ⊤ ∨ P' = ⊤ := by
  let R : Submodule ℂ (⨂[ℂ] i, V i) := Submodule.span ℂ {x | ∃ (f : ∀ i, V i) (i : ι), f i ∈ K i ∧ x = tprod ℂ f}
  have hR : ∀ (f : ∀ i, V i) i, f i ∈ K i → tprod ℂ f ∈ R := fun f i h => Submodule.subset_span ⟨f, i, h, rfl⟩
  have Rst : ∀ i a, R ≤ R.comap (map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a))) := fun i a =>
    Submodule.span_le.2 (by
      rintro _ ⟨f, j, hj, rfl⟩
      show map _ (tprod ℂ f) ∈ R
      rw [map_tprod]
      refine hR _ j ?_
      by_cases h : j = i
      · subst h; simpa using h2 j a _ hj
      · simpa [Function.update_of_ne h] using hj)
  have nak : ∀ Q : Submodule ℂ (⨂[ℂ] i, V i), (∀ (f : ∀ i, V i) i, f i ∈ Z i → tprod ℂ f ∈ Q) →
      (∀ i a, ∀ x ∈ Q, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ Q) →
      Q ⊔ R = ⊤ → Q = ⊤ := fun Q q1 q2 q3 => by
    have fin : ∀ x ∈ R, ∃ t : ∀ i, List (V i), (∀ i, ∀ y ∈ t i, y ∈ K i) ∧
        ∀ u : ∀ i, Module.End ℂ (V i), (∀ i, ∀ y ∈ t i, u i y ∈ Z i) → map u x ∈ Q := fun x hx => by
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨f, i, hi, rfl⟩ := hx
        refine ⟨Function.update (fun _ => []) i [f i], fun j y hy => ?_, fun u hu => ?_⟩
        · by_cases h : j = i
          · subst h
            rw [Function.update_self, List.mem_singleton] at hy
            exact hy ▸ hi
          · simp [Function.update_of_ne h] at hy
        · rw [map_tprod]
          exact q1 _ i (hu i _ (by simp))
      | zero => exact ⟨fun _ => [], by simp, fun u _ => by simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨s, s1, s2⟩ := ha
        obtain ⟨t, t1, t2⟩ := hb
        refine ⟨fun i => s i ++ t i, fun i y hy => (List.mem_append.1 hy).elim (s1 i y) (t1 i y), fun u hu => ?_⟩
        rw [map_add]
        exact Q.add_mem (s2 u fun i y hy => hu i y (List.mem_append_left _ hy))
          (t2 u fun i y hy => hu i y (List.mem_append_right _ hy))
      | smul c a _ ha =>
        obtain ⟨s, s1, s2⟩ := ha
        exact ⟨s, s1, fun u hu => by rw [map_smul]; exact Q.smul_mem c (s2 u hu)⟩
    obtain ⟨p, hp, x, hx, e⟩ := Submodule.mem_sup.1 (q3 ▸ Submodule.mem_top : tprod ℂ v ∈ Q ⊔ R)
    obtain ⟨t, t1, t2⟩ := fin x hx
    refine eq_top_iff.2 fun y _ => ?_
    induction y using PiTensorProduct.induction_on with
    | smul_tprod c f =>
      choose u u1 u2 u3 using fun i => h4 i (t i) (t1 i) (f i)
      have a1 : map u (tprod ℂ v) ∈ Q := by
        rw [← e, map_add]
        exact Q.add_mem (map_st act Q q2 u u1 p hp) (t2 u u3)
      have a2 : map u (tprod ℂ v) - tprod ℂ f ∈ Q := ker_le Z Q q1 (by
        rw [LinearMap.mem_ker, map_sub, map_tprod, map_tprod, map_tprod, sub_eq_zero]
        congr 1
        funext i
        exact (Submodule.Quotient.eq _).2 (u2 i))
      exact Q.smul_mem c (by simpa using Q.sub_mem a1 a2)
    | add x y hx hy => exact Q.add_mem (hx trivial) (hy trivial)
  have le : ∀ Q : Submodule ℂ (⨂[ℂ] i, V i), (∀ (f : ∀ i, V i) i, f i ∈ Z i → tprod ℂ f ∈ Q) →
      (∀ i a, ∀ x ∈ Q, map (Function.update (fun j => (LinearMap.id : V j →ₗ[ℂ] V j)) i (act i a)) x ∈ Q) →
      Q ≤ R ∨ Q = ⊤ := fun Q q1 q2 =>
    (tens_max act K hr h1 h2 h3 R hR (Q ⊔ R) le_sup_right (fun i a x hx => by
      obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add]
      exact Submodule.add_mem_sup (q2 i a p hp) (Rst i a hy))).imp (le_sup_left.trans ·) (nak Q q1 q2)
  rcases le P hZ hP with a | a
  · rcases le P' hZ' hP' with b | b
    · exact Or.inl (nak P hZ hP (top_le_iff.1 (e ▸ sup_le le_sup_left (b.trans le_sup_right))))
    · exact Or.inr b
  · exact Or.inl a
end PositivityTheory.ThKR.Join
