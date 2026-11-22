-- Prove2me | solution 1 for ParallelPostulate.Hilbert.model_dedekind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:17.913679+00:00
-- url     : https://prove2.me/submissions/1aab6796-bc56-44c5-bd8c-74545352a359

module
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Definitions.Def_LeanPool_ParallelPostulate_Hilbert
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_LeanPool_ParallelPostulate
public import Theorems.Thm_ParallelPostulate_Hilbert_cut_point
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_between_pt_of_strictBetween
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_pt_mem_plane_of_le
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_strictBetween_of_between_pt
public import Theorems.Thm_ParallelPostulate_Pairs_Dim_pt_injective


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.Hilbert
open Pairs HyperbolicPlane
namespace ParallelPostulate.Hilbert
theorem _root_.solution (κ : ℝ) (hκ : κ ≤ 0) : (model κ hκ).Dedekind := by
  intro l S T hST hdisj hSne hTne hS hT
  obtain ⟨M, hM, hl, -⟩ := l.2
  have hlies : ∀ X : Pt κ, (model κ hκ).lies X l ↔ X.1 ∈ M.points := by
    intro X
    change X.1 ∈ l.1 ↔ _
    rw [hl]
    exact ⟨fun h => h.1, fun h => ⟨h, X.2⟩⟩
  let I : Set ℝ := {t | M.pt t ∈ plane κ}
  let S' : Set ℝ := {t | ∃ h : M.pt t ∈ plane κ, (⟨M.pt t, h⟩ : Pt κ) ∈ S}
  let T' : Set ℝ := {t | ∃ h : M.pt t ∈ plane κ, (⟨M.pt t, h⟩ : Pt κ) ∈ T}
  have hpar : ∀ X : Pt κ, (model κ hκ).lies X l → ∃ t, ∃ h : M.pt t ∈ plane κ,
      X = ⟨M.pt t, h⟩ := by
    intro X hX
    obtain ⟨t, ht⟩ := (hlies X).mp hX
    exact ⟨t, ht ▸ X.2, Subtype.ext ht.symm⟩
  have hI : ∀ a ∈ I, ∀ b ∈ I, ∀ c, a ≤ c → c ≤ b → c ∈ I :=
    fun a ha b hb c hac hcb => pt_mem_plane_of_le M ha hb hac hcb
  have hST' : ∀ t, t ∈ I ↔ t ∈ S' ∨ t ∈ T' := by
    intro t
    constructor
    · intro h
      rcases (hST ⟨M.pt t, h⟩).mp ((hlies _).mpr ⟨t, rfl⟩) with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  have hdisj' : ∀ t ∈ S', t ∉ T' := fun t ⟨h, hs⟩ ⟨_, ht⟩ => hdisj _ hs ht
  have hne' : ∀ {U : Set (Pt κ)} {U' : Set ℝ}, (∀ X ∈ U, (model κ hκ).lies X l) →
      U' = {t | ∃ h : M.pt t ∈ plane κ, (⟨M.pt t, h⟩ : Pt κ) ∈ U} → U.Nonempty →
      U'.Nonempty := by
    rintro U U' hU rfl ⟨X, hX⟩
    obtain ⟨t, h, rfl⟩ := hpar X (hU X hX)
    exact ⟨t, h, hX⟩
  have hSl : ∀ X ∈ S, (model κ hκ).lies X l := fun X hX => (hST X).mpr (Or.inl hX)
  have hTl : ∀ X ∈ T, (model κ hκ).lies X l := fun X hX => (hST X).mpr (Or.inr hX)
  have hS' : ∀ x ∈ S', ∀ y ∈ T', ∀ z ∈ T', ¬ StrictBetween y x z :=
    fun x ⟨hx, hxS⟩ y ⟨hy, hyT⟩ z ⟨hz, hzT⟩ h =>
      hS _ hxS _ hyT _ hzT (between_pt_of_strictBetween M hM h)
  have hT' : ∀ x ∈ T', ∀ y ∈ S', ∀ z ∈ S', ¬ StrictBetween y x z :=
    fun x ⟨hx, hxT⟩ y ⟨hy, hyS⟩ z ⟨hz, hzS⟩ h =>
      hT _ hxT _ hyS _ hzS (between_pt_of_strictBetween M hM h)
  obtain ⟨c, ⟨hcI, hc⟩, huniq⟩ := cut_point hI hST' hdisj' (hne' hSl rfl hSne)
    (hne' hTl rfl hTne) hS' hT'
  refine ⟨⟨M.pt c, hcI⟩, ⟨(hlies _).mpr ⟨c, rfl⟩, ?_⟩, ?_⟩
  · intro A hA B hB hAQ hBQ
    obtain ⟨a, ha, rfl⟩ := hpar A (hSl A hA)
    obtain ⟨b, hb, rfl⟩ := hpar B (hTl B hB)
    exact between_pt_of_strictBetween M hM (hc a ⟨ha, hA⟩ b ⟨hb, hB⟩
      (fun e => hAQ (by subst e; rfl)) (fun e => hBQ (by subst e; rfl)))
  · rintro Q ⟨hQl, hQ⟩
    obtain ⟨c', hc', rfl⟩ := hpar Q hQl
    have := huniq c' ⟨hc', fun a ⟨ha, hA⟩ b ⟨hb, hB⟩ hac hbc =>
      strictBetween_of_between_pt M hM (hQ _ hA _ hB
        (fun e => hac (M.pt_injective hM (congrArg Subtype.val e)))
        (fun e => hbc (M.pt_injective hM (congrArg Subtype.val e))))⟩
    subst this
    rfl
end ParallelPostulate.Hilbert
