-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassFin.sub_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:44:44.671892+00:00
-- url     : https://prove2.me/submissions/88cd5425-38ed-4aca-8991-0c8b22dd4f40

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_ClassFiniteOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_HermSingleLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassFin
open PI.HermLatFin
variable {E : Type} [Field E] {M : ℕ} (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E)
variable [NumberField E]
namespace PI.UnitaryGroupMassFormula.UJClassFin
theorem _root_.solution (N : Submodule (𝓞 E) (Fin M → E)) (hN : N.FG) (n : ℕ) (hn : 0 < n) :
    {s : Set (Fin M → E) | (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧
      (∀ x ∈ N, (n : E) • x ∈ s) ∧ s ⊆ N}.Finite := by
  classical
  haveI : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 hN
  haveI : Module.Finite ℤ N := Module.Finite.trans (𝓞 E) N
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := N)

  let rep : (S → Fin n) → (Fin M → E) := fun c => ∑ g : S, ((c g : ℕ) : ℤ) • ((g : N) : Fin M → E)
  let T : Set (Fin M → E) := Set.range rep
  have hT : T.Finite := Set.finite_range rep
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  have hdec : ∀ x ∈ N, ∃ t ∈ T, ∃ z ∈ N, x = t + (n : E) • z := by
    intro x hx
    have hmem : (⟨x, hx⟩ : N) ∈ Submodule.span ℤ (S : Set N) := by rw [hS]; trivial
    obtain ⟨a, -, ha⟩ := Submodule.mem_span_finset.1 hmem
    have hx' : x = ∑ g ∈ S, a g • ((g : N) : Fin M → E) := by
      have := congrArg Subtype.val ha
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    let c : S → Fin n := fun g => ⟨(a g % n).toNat, by
      have h1 := Int.emod_nonneg (a g) hnZ.ne'
      have h2 := Int.emod_lt_of_pos (a g) hnZ
      omega⟩
    refine ⟨rep c, ⟨c, rfl⟩, ∑ g ∈ S, (a g / n) • ((g : N) : Fin M → E), ?_, ?_⟩
    · exact Submodule.sum_mem _ fun g _ => Submodule.smul_of_tower_mem _ _ g.2
    · have hc : ∀ g : S, (((c g : ℕ) : ℤ)) = a g % n := fun g => by
        simp only [c]
        exact Int.toNat_of_nonneg (Int.emod_nonneg _ hnZ.ne')
      simp only [rep, hc]
      rw [Finset.sum_coe_sort S (fun g => (a g % (n : ℤ)) • ((g : N) : Fin M → E)), hx',
        Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← Int.cast_smul_eq_zsmul E, smul_comm ((n : E)) _ _, ← Int.cast_smul_eq_zsmul E (a g / n),
        smul_smul, ← Int.cast_smul_eq_zsmul E (a g % n), ← add_smul]
      congr 1
      have h2 : ((a g : ℤ) : E) = ((a g % n : ℤ) : E) + (n : E) * ((a g / n : ℤ) : E) := by
        have hdm : a g % (n : ℤ) + (n : ℤ) * (a g / n) = a g := by
          first
            | exact Int.emod_add_ediv _ _
            | exact Int.emod_add_ediv' _ _
            | (rw [Int.emod_def]; ring)
            | exact EuclideanDomain.mod_add_div _ _
        have := congrArg (fun q : ℤ => (q : E)) hdm
        push_cast at this
        rw [this]
      rw [h2]
      ring

  have key : ∀ s s' : Set (Fin M → E), s ∈ {s : Set (Fin M → E) |
      (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧
        (∀ x ∈ N, (n : E) • x ∈ s) ∧ s ⊆ N} → s' ∈ {s : Set (Fin M → E) |
      (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧
        (∀ x ∈ N, (n : E) • x ∈ s) ∧ s ⊆ N} → s ∩ T = s' ∩ T → s ⊆ s' := by
    rintro s s' ⟨⟨G, hG⟩, hns, hsN⟩ ⟨⟨G', hG'⟩, hns', -⟩ heq x hx
    obtain ⟨t, ht, z, hz, rfl⟩ := hdec x (hsN hx)
    rw [← hG] at hx hns
    rw [← hG'] at hns' ⊢
    have hts : t ∈ G := by
      have := G.sub_mem hx (hns z hz)
      simpa using this
    have hts' : t ∈ s' ∩ T := heq ▸ ⟨(show t ∈ s by rw [← hG]; exact hts), ht⟩
    rw [← hG'] at hts'
    exact G'.add_mem hts'.1 (hns' z hz)
  refine Set.Finite.of_finite_image (f := fun s => s ∩ T) ?_ ?_
  · refine (hT.finite_subsets).subset ?_
    rintro _ ⟨s, -, rfl⟩
    exact Set.inter_subset_right
  · intro s hs s' hs' heq
    exact Set.Subset.antisymm (key s s' hs hs' heq) (key s' s hs' hs heq.symm)
end PI.UnitaryGroupMassFormula.UJClassFin
