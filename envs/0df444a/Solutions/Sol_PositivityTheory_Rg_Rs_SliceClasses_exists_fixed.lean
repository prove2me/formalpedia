-- Prove2me | solution 1 for PositivityTheory.Rg.Rs.SliceClasses.exists_fixed
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:57:02.332514+00:00
-- url     : https://prove2.me/submissions/028f4b93-307a-4920-9676-098680492f16

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_SliceTensors_PSliceC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.SliceClasses
theorem _root_.solution {U : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] {ι : Type*}
    (M : ι → Module.End ℂ U) (hc : ∀ i j, Commute (M i) (M j)) (Φ : U →ₗ[ℂ] ℂ) (hΦ : Φ ≠ 0)
    (hinv : ∀ i, Φ ∘ₗ M i = Φ) : ∃ w, w ≠ 0 ∧ ∀ i, M i w = w := by
  classical
  -- commuting unipotent operators on a nonzero space have a common fixed vector
  have uni : ∀ n : ℕ, ∀ (V : Type u_1) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V], Module.finrank ℂ V = n →
      ∀ (A : ι → Module.End ℂ V), (∀ i j, Commute (A i) (A j)) → (∀ i, IsNilpotent (A i - 1)) → Nontrivial V →
      ∃ w : V, w ≠ 0 ∧ ∀ i, A i w = w := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro V _ _ _ hn A hA hN hV
      by_cases hall : ∀ i, A i = 1
      · obtain ⟨w, hw⟩ := exists_ne (0 : V)
        exact ⟨w, hw, fun i => by rw [hall i]; rfl⟩
      push Not at hall
      obtain ⟨i0, hi0⟩ := hall
      set K0 := LinearMap.ker (A i0 - 1) with hK
      have hKne : K0 ≠ ⊥ := by
        intro h
        obtain ⟨k, hk⟩ := hN i0
        have hinj : Function.Injective ⇑(A i0 - 1 : Module.End ℂ V) := LinearMap.ker_eq_bot.1 h
        have hinjk : Function.Injective ((A i0 - 1) ^ k : Module.End ℂ V) := by
          rw [Module.End.coe_pow]; exact hinj.iterate k
        rw [hk] at hinjk
        obtain ⟨w, hw⟩ := exists_ne (0 : V)
        exact hw (hinjk (a₂ := 0) (by simp))
      have hKtop : K0 ≠ ⊤ := by
        intro h
        apply hi0
        have : A i0 - 1 = 0 := LinearMap.ker_eq_top.1 h
        exact sub_eq_zero.1 this
      have hinv' : ∀ j, ∀ x ∈ K0, A j x ∈ K0 := by
        intro j x hx
        have hc : Commute (A i0 - 1) (A j) := (hA i0 j).sub_left (Commute.one_left _)
        have := LinearMap.congr_fun hc.eq x
        simp only [Module.End.mul_apply] at this
        rw [hK, LinearMap.mem_ker] at hx ⊢
        rw [this, hx, map_zero]
      let B : ι → Module.End ℂ K0 := fun j => (A j).restrict (hinv' j)
      have hBc : ∀ i j, Commute (B i) (B j) := by
        intro i j
        refine LinearMap.ext fun x => Subtype.ext ?_
        exact LinearMap.congr_fun (hA i j).eq x.1
      have hBn : ∀ j, IsNilpotent (B j - 1) := by
        intro j
        have hm : ∀ x ∈ K0, (A j - 1) x ∈ K0 := fun x hx => by
          have := K0.sub_mem (hinv' j x hx) hx
          simpa using this
        have e : B j - 1 = (A j - 1).restrict hm := by
          refine LinearMap.ext fun x => Subtype.ext ?_
          rfl
        rw [e]
        exact Module.End.isNilpotent.restrict hm (hN j)
      have hlt : Module.finrank ℂ K0 < n := hn ▸ Submodule.finrank_lt hKtop
      obtain ⟨w, hw, hfix⟩ := ih _ hlt K0 rfl B hBc hBn (Submodule.nontrivial_iff_ne_bot.2 hKne)
      exact ⟨w.1, fun h => hw (Subtype.ext h), fun j => congrArg Subtype.val (hfix j)⟩
  -- reduce to the unipotent case
  have main : ∀ n : ℕ, ∀ (V : Type u_1) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V], Module.finrank ℂ V = n →
      ∀ (A : ι → Module.End ℂ V), (∀ i j, Commute (A i) (A j)) → ∀ Ψ : V →ₗ[ℂ] ℂ, Ψ ≠ 0 → (∀ i, Ψ ∘ₗ A i = Ψ) →
      ∃ w : V, w ≠ 0 ∧ ∀ i, A i w = w := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro V _ _ _ hn A hA Ψ hΨ hΨA
      have hVnt : Nontrivial V := by
        by_contra h
        rw [not_nontrivial_iff_subsingleton] at h
        exact hΨ (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])
      by_cases hall : ∀ i, IsNilpotent (A i - 1)
      · exact uni n V hn A hA hall hVnt
      push Not at hall
      obtain ⟨i0, hi0⟩ := hall
      set N : Module.End ℂ V := A i0 - 1 with hNdef
      obtain ⟨k, hk0, hk⟩ : ∃ k, k ≠ 0 ∧ IsCompl (LinearMap.ker (N ^ k)) (LinearMap.range (N ^ k)) := by
        obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 N.eventually_isCompl_ker_pow_range_pow
        exact ⟨k + 1, Nat.succ_ne_zero k, hk (k + 1) (Nat.le_succ k)⟩
      set G := LinearMap.ker (N ^ k) with hG
      have hΨN : Ψ ∘ₗ N = 0 := by
        rw [hNdef, LinearMap.comp_sub, hΨA i0, Module.End.one_eq_id, LinearMap.comp_id, sub_self]
      have hRΨ : ∀ x ∈ LinearMap.range (N ^ k), Ψ x = 0 := by
        rintro _ ⟨y, rfl⟩
        obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        rw [pow_succ', Module.End.mul_apply]
        exact LinearMap.congr_fun hΨN _
      have hGinv : ∀ j, ∀ x ∈ G, A j x ∈ G := by
        intro j x hx
        have hc : Commute (N ^ k) (A j) := ((hA i0 j).sub_left (Commute.one_left _)).pow_left k
        have := LinearMap.congr_fun hc.eq x
        simp only [Module.End.mul_apply] at this
        rw [hG, LinearMap.mem_ker] at hx ⊢
        rw [this, hx, map_zero]
      have hGtop : G ≠ ⊤ := by
        intro h
        exact hi0 ⟨k, LinearMap.ker_eq_top.1 h⟩
      let B : ι → Module.End ℂ G := fun j => (A j).restrict (hGinv j)
      have hBc : ∀ i j, Commute (B i) (B j) := by
        intro i j
        refine LinearMap.ext fun x => Subtype.ext ?_
        exact LinearMap.congr_fun (hA i j).eq x.1
      have hΨG : Ψ ∘ₗ G.subtype ≠ 0 := by
        intro h
        apply hΨ
        refine LinearMap.ext fun x => ?_
        have hx : x ∈ G ⊔ LinearMap.range (N ^ k) := by rw [hk.sup_eq_top]; exact Submodule.mem_top
        obtain ⟨g, hg, r, hr, rfl⟩ := Submodule.mem_sup.1 hx
        have : Ψ g = 0 := LinearMap.congr_fun h ⟨g, hg⟩
        rw [map_add, this, hRΨ r hr, add_zero, LinearMap.zero_apply]
      have hlt : Module.finrank ℂ G < n := hn ▸ Submodule.finrank_lt hGtop
      obtain ⟨w, hw, hfix⟩ := ih _ hlt G rfl B hBc (Ψ ∘ₗ G.subtype) hΨG (fun j => LinearMap.ext fun x => LinearMap.congr_fun (hΨA j) x.1)
      exact ⟨w.1, fun h => hw (Subtype.ext h), fun j => congrArg Subtype.val (hfix j)⟩
  exact main _ U rfl M hc Φ hΦ hinv

