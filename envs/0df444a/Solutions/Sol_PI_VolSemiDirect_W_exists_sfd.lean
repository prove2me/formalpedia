-- Prove2me | solution 1 for PI.VolSemiDirect.W.exists_sfd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:42.39035+00:00
-- url     : https://prove2.me/submissions/2bb94dbf-fbd8-48c8-b3eb-d653dd4b11ae

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_FundamentalDomainExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open MeasureTheory
namespace PI.VolSemiDirect.W
theorem _root_.solution {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Λ : Subgroup G)
    [DiscreteTopology Λ] :
    ∃ 𝓕 : Set G, MeasurableSet 𝓕 ∧ ∀ x : G, ∃! γ : Λ, γ • x ∈ 𝓕 := by
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.mp (isOpen_discrete ({1} : Set Λ))
  have hV1 : ∀ γ : Λ, (γ : G) ∈ V ↔ γ = 1 := fun γ => Set.ext_iff.mp hV γ
  have h1V : (1 : G) ∈ V := (hV1 1).mpr rfl
  obtain ⟨W, hWo, hW1, hWV⟩ := exists_open_nhds_one_split (hVo.mem_nhds h1V)
  obtain ⟨U, hUo, hU1, hUinv, hUV⟩ : ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ (∀ g ∈ U, g⁻¹ ∈ U) ∧
      ∀ a ∈ U, ∀ b ∈ U, a * b⁻¹ ∈ V :=
    ⟨W ∩ (fun g => g⁻¹) ⁻¹' W, hWo.inter (hWo.preimage continuous_inv), ⟨hW1, by simpa using hW1⟩,
      fun g hg => ⟨hg.2, by simpa using hg.1⟩, fun a ha b hb => hWV a ha.1 _ hb.2⟩
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq G

  have hB : ∀ x : G, ∃ n, x * (d n)⁻¹ ∈ U := by
    intro x
    obtain ⟨n, hn⟩ := hd.exists_mem_open
      (hUo.preimage (continuous_id.mul continuous_const) : IsOpen ((fun y => y * x⁻¹) ⁻¹' U))
      ⟨x, by simpa using hU1⟩
    refine ⟨n, ?_⟩
    have := hUinv _ hn
    simpa [mul_inv_rev] using this

  have hBu : ∀ (n : ℕ) (γ γ' : Λ) (x : G), (γ : G) * x * (d n)⁻¹ ∈ U →
      (γ' : G) * x * (d n)⁻¹ ∈ U → γ = γ' := by
    intro n γ γ' x h h'
    have hm := hUV _ h _ h'
    have : ((γ * γ'⁻¹ : Λ) : G) ∈ V := by
      convert hm using 1
      push_cast
      group
    rw [hV1, mul_inv_eq_one] at this
    exact this

  obtain ⟨S, hS, hSo⟩ : ∃ S : ℕ → Set G, (∀ m x, x ∈ S m ↔ ∃ γ : Λ, (γ : G) * x * (d m)⁻¹ ∈ U) ∧
      ∀ m, IsOpen (S m) :=
    ⟨fun m => ⋃ γ : Λ, (fun x => (γ : G) * x * (d m)⁻¹) ⁻¹' U, fun m x => by simp,
      fun m => isOpen_iUnion fun γ =>
        hUo.preimage ((continuous_const.mul continuous_id).mul continuous_const)⟩
  have hinv : ∀ (γ : Λ) (y : G) (m : ℕ), (γ : G) * y ∈ S m ↔ y ∈ S m := by
    intro γ y m
    rw [hS, hS]
    constructor
    · rintro ⟨δ, hδ⟩
      exact ⟨δ * γ, by push_cast; simpa [mul_assoc] using hδ⟩
    · rintro ⟨δ, hδ⟩
      exact ⟨δ * γ⁻¹, by push_cast; simpa [mul_assoc] using hδ⟩
  obtain ⟨F, hF, hFm⟩ : ∃ F : Set G, (∀ y, y ∈ F ↔ ∃ n, y * (d n)⁻¹ ∈ U ∧ ∀ m < n, y ∉ S m) ∧
      MeasurableSet F := by
    refine ⟨⋃ n, ((fun x => x * (d n)⁻¹) ⁻¹' U \ ⋃ m, ⋃ (_ : m < n), S m), fun y => ?_, ?_⟩
    · simp only [Set.mem_iUnion, Set.mem_diff, Set.mem_preimage, not_exists]
    · exact MeasurableSet.iUnion fun n =>
        (hUo.preimage (continuous_id.mul continuous_const)).measurableSet.diff
          (isOpen_iUnion fun m => isOpen_iUnion fun _ => hSo m).measurableSet
  refine ⟨F, hFm, fun x => ?_⟩
  have hex : ∃ n, x ∈ S n := by
    obtain ⟨n, hn⟩ := hB x
    exact ⟨n, (hS n x).mpr ⟨1, by simpa using hn⟩⟩
  classical
  obtain ⟨n0, hn0x, hmin⟩ : ∃ n0, x ∈ S n0 ∧ ∀ m < n0, x ∉ S m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  obtain ⟨γ, hγ⟩ := (hS n0 x).mp hn0x
  refine ⟨γ, ?_, ?_⟩
  · change (γ : G) * x ∈ F
    rw [hF]
    exact ⟨n0, hγ, fun m hm h => hmin m hm ((hinv γ x m).mp h)⟩
  · intro γ' hγ'
    change (γ' : G) * x ∈ F at hγ'
    rw [hF] at hγ'
    obtain ⟨n, hn, hnmin⟩ := hγ'
    have hxn : x ∈ S n := (hS n x).mpr ⟨γ', hn⟩
    have hn0 : n = n0 := by
      apply le_antisymm
      · by_contra hlt
        push_neg at hlt
        exact hnmin n0 hlt ((hinv γ' x n0).mpr hn0x)
      · exact not_lt.mp fun h => hmin n h hxn
    rw [hn0] at hn
    exact hBu n0 γ' γ x hn hγ
end PI.VolSemiDirect.W
