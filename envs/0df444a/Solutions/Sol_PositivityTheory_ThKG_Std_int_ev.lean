-- Prove2me | solution 1 for PositivityTheory.ThKG.Std.int_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:23:08.684926+00:00
-- url     : https://prove2.me/submissions/d33716e3-e971-423b-8f0a-ebed37443c27

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_SplitProd
import Theorems.Thm_PositivityTheory_ThKG_Std_ext_mid
import Theorems.Thm_PositivityTheory_ThKG_Std_ext_off
import Theorems.Thm_PositivityTheory_ThKG_Std_prod_mid
import Theorems.Thm_PositivityTheory_ThKG_Std_prod_vol
import Theorems.Thm_PositivityTheory_ThKG_Std_split_prod
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf



set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n d n₁ d₁ : ℕ} {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}
variable {jr : Fin n₁ → Fin n} {jc : Fin d₁ → Fin d}
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] {m : Measure k} {ψ : AddChar k ℂ}
namespace PositivityTheory.ThKG.Std
theorem _root_.solution (hm : IsVol m) (hϖ : IsUnif ϖ) {jc : Fin d₁ → Fin d} (hc : Function.Injective jc) {e : Fin n → Fin d}
    {e₁ : Fin n → Fin d₁} (he : ∀ i, jc (e₁ i) = e i) (j₀ : Fin d) (h0 : j₀ ∉ Set.range e) (h1 : ∀ j, j₀ ≠ jc j)
    (y : Matrix (Fin n) (Fin d₁) k) :
    ∫ Z, std ν ϖ c e (tm (cut (Finset.univ.filter fun p => p.2 = j₀) Z) + ext id jc y) * wt (Finset.univ.filter fun p => p.2 = j₀) Z
      ∂(Measure.pi fun _ => m) = (((resCard k : ℂ) ^ c)⁻¹) ^ n * std ν ϖ c e₁ y := by
  haveI := hm.haar
  set P : Finset (Fin n × Fin d) := Finset.univ.filter fun p => p.2 = j₀ with hP
  have hY : ∀ p ∈ P, ext id jc y p.1 p.2 = 0 := fun p hp => ext_off y (Or.inr fun j => by
    rw [(Finset.mem_filter.1 hp).2]; exact h1 j)
  have hd : ∀ Z, (tm (cut P Z) + ext id jc y).submatrix id e = y.submatrix id e₁ := fun Z => by
    ext i j
    have : e j ≠ j₀ := fun h => h0 ⟨j, h⟩
    have h2 := ext_mid Function.injective_id hc y i (e₁ j)
    rw [he] at h2
    simpa [tm, cut, hP, this] using h2
  simp only [std, hd, mul_right_comm _ (dl ν _), split_prod P _ hY]
  rw [integral_mul_const, integral_const_mul, integral_fintype_prod_eq_prod
    (fun (p : Fin n × Fin d) x => if p ∈ P then ind (rad ϖ c e p.2) x else ind 1 x),
    prod_vol hm hϖ (fun i => (i, j₀)) (fun _ _ h => (Prod.ext_iff.1 h).1) (fun p => ?_),
    prod_mid Function.injective_id hc (e₁ := e₁) (fun j => ?_) (fun i j h => h1 j (Finset.mem_filter.1 h).2.symm)]
  · ring
  · exact ⟨fun ⟨i, hi⟩ => ⟨i, hc ((he i).trans hi)⟩, fun ⟨i, hi⟩ => ⟨i, by rw [← he, hi]⟩⟩
  · simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ ⟨rfl, h0⟩, fun h => ⟨p.1, Prod.ext rfl h.1.symm⟩⟩
end PositivityTheory.ThKG.Std
