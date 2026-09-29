-- Prove2me | solution 1 for Submodule.free_of_free_of_isPrincipalIdealRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/5ad90e8c-a5af-5a99-8746-e0f7bec2b09a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_free_of_free_of_isPrincipalIdealRing

set_option autoImplicit false
universe u v

set_option maxHeartbeats 3200000

theorem solution {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Free R M] (N : Submodule R M) :
    Module.Free R N := by
  classical

  obtain ⟨⟨ι, b⟩⟩ := (inferInstance : Module.Free R M)
  letI : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  haveI : WellFoundedLT ι := ⟨(IsWellOrder.toIsWellFounded (r := WellOrderingRel)).wf⟩

  let F : ι → Submodule R M := fun i =>
    { carrier := {x | ∀ j, i < j → b.repr x j = 0}
      add_mem' := fun {x y} hx hy j hj => by rw [map_add, Finsupp.add_apply, hx j hj, hy j hj, add_zero]
      zero_mem' := fun j _ => by rw [map_zero, Finsupp.zero_apply]
      smul_mem' := fun c x hx j hj => by rw [map_smul, Finsupp.smul_apply, hx j hj, smul_zero] }
  have memF : ∀ {i x}, x ∈ F i ↔ ∀ j, i < j → b.repr x j = 0 := fun {i x} => Iff.rfl

  let lead : ∀ x : M, x ≠ 0 → ι := fun x hx =>
    (b.repr x).support.max' (Finsupp.support_nonempty_iff.2 (by rwa [ne_eq, LinearEquiv.map_eq_zero_iff]))
  have lead_mem_support : ∀ x (hx : x ≠ 0), lead x hx ∈ (b.repr x).support := fun x hx => Finset.max'_mem _ _
  have le_lead : ∀ x (hx : x ≠ 0) j, b.repr x j ≠ 0 → j ≤ lead x hx := fun x hx j hj =>
    Finset.le_max' _ _ (Finsupp.mem_support_iff.2 hj)
  have mem_F_lead : ∀ x (hx : x ≠ 0), x ∈ F (lead x hx) := fun x hx j hj => by
    by_contra h
    exact (not_lt.2 (le_lead x hx j h)) hj
  have lead_lt : ∀ x (hx : x ≠ 0) i, x ∈ F i → b.repr x i = 0 → lead x hx < i := fun x hx i hF hi => by
    rcases lt_trichotomy (lead x hx) i with h | h | h
    · exact h
    · exact absurd (h ▸ hi) (Finsupp.mem_support_iff.1 (lead_mem_support x hx))
    · exact absurd (hF _ h) (Finsupp.mem_support_iff.1 (lead_mem_support x hx))

  let I : ι → Ideal R := fun i => (N ⊓ F i).map (b.coord i)
  let a : ι → R := fun i => Submodule.IsPrincipal.generator (I i)
  have hIa : ∀ i, I i = Ideal.span {a i} := fun i => (Submodule.IsPrincipal.span_singleton_generator (I i)).symm
  have ha_mem : ∀ i, a i ∈ I i := fun i => Submodule.IsPrincipal.generator_mem (I i)
  have hn : ∀ i, ∃ n : M, n ∈ N ∧ n ∈ F i ∧ b.repr n i = a i := fun i => by
    obtain ⟨n, ⟨hnN, hnF⟩, hn⟩ := Submodule.mem_map.1 (ha_mem i)
    exact ⟨n, hnN, hnF, hn⟩
  choose n hnN hnF hna using hn

  let S : Set ι := {i | a i ≠ 0}
  let v : S → N := fun i => ⟨n i, hnN i⟩
  have hv : ∀ i : S, ((v i : N) : M) = n i := fun i => rfl

  have repr_n_of_lt : ∀ {i j : ι}, j < i → b.repr (n j) i = 0 := fun {i j} h => hnF j i h

  have hli : LinearIndependent R v := by
    rw [linearIndependent_iff']
    intro s c hsum
    by_contra hne
    push Not at hne
    obtain ⟨i₁, hi₁s, hci₁⟩ := hne

    let T : Finset S := s.filter fun i => c i ≠ 0
    have hT : T.Nonempty := ⟨i₁, Finset.mem_filter.2 ⟨hi₁s, hci₁⟩⟩
    let i₀ : S := T.max' hT
    have hi₀T : i₀ ∈ T := Finset.max'_mem T hT
    have hci₀ : c i₀ ≠ 0 := (Finset.mem_filter.1 hi₀T).2
    have hmax : ∀ i ∈ s, c i ≠ 0 → i ≤ i₀ := fun i hi hci => Finset.le_max' T i (Finset.mem_filter.2 ⟨hi, hci⟩)

    have h0 := congrArg (fun x : N => b.repr (x : M) (i₀ : ι)) hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, Submodule.coe_zero, map_zero, Finsupp.zero_apply] at h0
    rw [Finset.sum_eq_single i₀] at h0
    · rw [hv, hna, smul_eq_mul] at h0
      exact hci₀ ((mul_eq_zero.1 h0).resolve_right i₀.2)
    · intro i his hne'
      by_cases hci : c i = 0
      · rw [hci, zero_smul]
      · have hlt : (i : ι) < i₀ := lt_of_le_of_ne (Subtype.coe_le_coe.2 (hmax i his hci)) (fun h => hne' (Subtype.ext h))
        rw [hv, repr_n_of_lt hlt, smul_zero]
    · intro h; exact absurd (Finset.mem_of_mem_filter _ hi₀T) h

  have hspanF : ∀ i, ∀ x : N, (x : M) ∈ F i → x ∈ Submodule.span R (Set.range v) := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      intro x hxF

      have hxi : b.repr (x : M) i ∈ I i := Submodule.mem_map.2 ⟨x, ⟨x.2, hxF⟩, rfl⟩
      rw [hIa, Ideal.mem_span_singleton'] at hxi
      obtain ⟨c, hc⟩ := hxi

      let y : N := if hi : a i ≠ 0 then x - c • v ⟨i, hi⟩ else x
      have hy_span : y ∈ Submodule.span R (Set.range v) → x ∈ Submodule.span R (Set.range v) := by
        intro hy
        by_cases hi : a i ≠ 0
        · have : x = y + c • v ⟨i, hi⟩ := by simp only [y, dif_pos hi, sub_add_cancel]
          rw [this]
          exact Submodule.add_mem _ hy (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩))
        · simp only [y, dif_neg hi] at hy
          exact hy
      apply hy_span
      have hyF : (y : M) ∈ F i := by
        by_cases hi : a i ≠ 0
        · simp only [y, dif_pos hi, Submodule.coe_sub, Submodule.coe_smul, hv]
          exact Submodule.sub_mem _ hxF (Submodule.smul_mem _ _ (hnF i))
        · simp only [y, dif_neg hi]; exact hxF
      have hyi : b.repr (y : M) i = 0 := by
        by_cases hi : a i ≠ 0
        · simp only [y, dif_pos hi, Submodule.coe_sub, Submodule.coe_smul, hv, map_sub, map_smul, Finsupp.sub_apply,
            Finsupp.smul_apply, hna, ← hc, smul_eq_mul, sub_self]
        · simp only [y, dif_neg hi]
          rw [← hc]
          push Not at hi
          rw [hi, mul_zero]
      by_cases hy0 : (y : M) = 0
      · have : y = 0 := Subtype.ext hy0
        rw [this]; exact Submodule.zero_mem _
      · exact ih (lead (y : M) hy0) (lead_lt _ hy0 i hyF hyi) y (mem_F_lead _ hy0)
  have hsp : ⊤ ≤ Submodule.span R (Set.range v) := by
    intro x _
    by_cases hx0 : (x : M) = 0
    · have : x = 0 := Subtype.ext hx0
      rw [this]; exact Submodule.zero_mem _
    · exact hspanF (lead (x : M) hx0) x (mem_F_lead _ hx0)
  exact Module.Free.of_basis (Module.Basis.mk hli hsp)

end S_Submodule_free_of_free_of_isPrincipalIdealRing
end P2MW
export P2MW.S_Submodule_free_of_free_of_isPrincipalIdealRing (solution)
