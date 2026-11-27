-- Prove2me | solution 1 for UpperTheory.Reformulated.B.ExistsPowSmulMem.exists_pow_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:32:48.894782+00:00
-- url     : https://prove2.me/submissions/7d1c7752-09e6-4a3d-8561-71cfd5674780

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPowSmulMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.ExistsPowSmulMem
theorem _root_.solution :
    ∀ {O K X : Type} [inst : CommRing O] [inst_1 : IsDomain O]
    [IsDiscreteValuationRing O] [inst_3 : Field K] [inst_4 : Algebra O K] [IsFractionRing O K] [inst_6 : AddCommGroup X]
    [inst_7 : _root_.Module K X] [inst_8 : _root_.Module O X] [IsScalarTower O K X] (ϖ : O),
    Irreducible ϖ →
      ∀ (A B : Submodule O X), A.FG → Submodule.span K (↑B : Set X) = ⊤ → ∃ (k : ℕ), ∀ a ∈ A, ϖ ^ k • a ∈ B := by
  intro O K X _ _ _ _ _ _ _ _ _ _ ϖ hϖ A B hA hB
  have h1 : ∀ x ∈ Submodule.span K (↑B : Set X), ∃ d : O, d ≠ 0 ∧ d • x ∈ B := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_ne_zero, B.smul_mem _ hx⟩
    | zero => exact ⟨1, one_ne_zero, B.smul_mem _ B.zero_mem⟩
    | add x y _ _ hx hy =>
      obtain ⟨d, hd, hdx⟩ := hx
      obtain ⟨e, he, hey⟩ := hy
      refine ⟨d * e, mul_ne_zero hd he, ?_⟩
      rw [smul_add]
      refine B.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact B.smul_mem _ hdx
      · rw [mul_smul]; exact B.smul_mem _ hey
    | smul r x _ hx =>
      obtain ⟨d, hd, hdx⟩ := hx
      obtain ⟨⟨n, e⟩, hne⟩ := IsLocalization.surj (nonZeroDivisors O) r
      refine ⟨d * e, mul_ne_zero hd (nonZeroDivisors.ne_zero e.2), ?_⟩
      have h : (e : O) • r • x = n • x := by
        rw [← algebraMap_smul K (e : O), smul_smul, mul_comm, hne, algebraMap_smul]
      rw [mul_smul, h, smul_smul, mul_comm, mul_smul]
      exact B.smul_mem _ hdx
  have h2 : ∀ x : X, ∃ k : ℕ, ϖ ^ k • x ∈ B := by
    intro x
    obtain ⟨d, hd, hdx⟩ := h1 x (hB ▸ Submodule.mem_top)
    obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd hϖ
    refine ⟨k, ?_⟩
    rw [← hu, mul_comm, mul_smul]
    exact B.smul_mem _ hdx
  choose f hf using h2
  obtain ⟨s, rfl⟩ := hA
  refine ⟨s.sup f, fun a ha => ?_⟩
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := f) (Finset.mem_coe.1 hx))
    rw [hm, add_comm, pow_add, mul_smul]
    exact B.smul_mem _ (hf x)
  | zero => exact B.smul_mem _ B.zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact B.add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact B.smul_mem _ hx
end UpperTheory.Reformulated.B.ExistsPowSmulMem
