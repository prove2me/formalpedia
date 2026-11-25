-- Prove2me | solution 1 for UpperTheory.compact_quotient_submodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:08:55.142695+00:00
-- url     : https://prove2.me/submissions/05984f7e-c353-419d-bf0d-0c629604135f

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CompactQuotientSubmodule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory
theorem _root_.solution :
    ∀ {LL O W Q : Type} [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup W] [Module LL W] [Module O W]
        [IsScalarTower O LL W] [TopologicalSpace LL] [TopologicalSpace W] [ContinuousSMul LL W]
        [IsTopologicalAddGroup W] [T2Space W] [AddCommGroup Q] [Module O Q] [Finite Q]
        (Z : Submodule O W) (p : O) (f : Z →ₗ[O] Q),
        IsCompact (Set.range (algebraMap O LL)) →
        (∀ U ∈ nhds (0 : W), ∃ n : ℕ, ∀ z ∈ Z, p ^ n • z ∈ U) →
        (∀ z : Z, f z = 0 → ∃ w ∈ Z, (z : W) = p • w) →
        Z.FG := by
  intro LL O W Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z p f hK hsmall hker
  classical
  have := Fintype.ofFinite Q
  let s : Q → Z := Function.invFun f
  have hs : ∀ z : Z, f (s (f z)) = f z := fun z => Function.invFun_eq ⟨z, rfl⟩
  let v : Q → W := fun q => (s q : W)
  let N : Submodule O W := Submodule.span O (Set.range v)
  have hNZ : N ≤ Z := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨q, rfl⟩
    exact (s q).2
  have hstep : ∀ z ∈ Z, ∃ a ∈ N, ∃ w ∈ Z, z = a + p • w := by
    intro z hz
    obtain ⟨w, hw, e⟩ := hker (⟨z, hz⟩ - s (f ⟨z, hz⟩)) (by rw [map_sub, hs, sub_self])
    refine ⟨v (f ⟨z, hz⟩), Submodule.subset_span ⟨_, rfl⟩, w, hw, ?_⟩
    rw [← e]
    simp [v]
  have hiter : ∀ n : ℕ, ∀ z ∈ Z, ∃ a ∈ N, ∃ w ∈ Z, z = a + p ^ n • w := by
    intro n
    induction n with
    | zero => exact fun z hz => ⟨0, N.zero_mem, z, hz, by simp⟩
    | succ n ih =>
      intro z hz
      obtain ⟨a, ha, w, hw, e⟩ := ih z hz
      obtain ⟨b, hb, u, hu, e'⟩ := hstep w hw
      refine ⟨a + p ^ n • b, N.add_mem ha (N.smul_mem _ hb), u, hu, ?_⟩
      rw [e, e', smul_add, smul_smul, pow_succ, add_assoc]
  have hcomp : IsCompact (N : Set W) := by
    have hc : Continuous (fun c : Q → LL => ∑ q, c q • v q) := by fun_prop
    have h1 := (isCompact_univ_pi (fun _ : Q => hK)).image hc
    convert h1 using 1
    ext x
    simp only [SetLike.mem_coe, N, Submodule.mem_span_range_iff_exists_fun, Set.mem_image]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨fun q => algebraMap O LL (c q), fun q _ => ⟨c q, rfl⟩, by simp⟩
    · rintro ⟨c, hc, rfl⟩
      choose d hd using fun q => hc q (Set.mem_univ q)
      exact ⟨d, by simp [← hd]⟩
  have hZN : Z ≤ N := by
    intro z hz
    by_contra hzN
    have hopen : IsOpen ((fun x : W => z - x) ⁻¹' (N : Set W)ᶜ) :=
      hcomp.isClosed.isOpen_compl.preimage (by fun_prop)
    obtain ⟨n, hn⟩ := hsmall _ (hopen.mem_nhds (by simpa using hzN))
    obtain ⟨a, ha, w, hw, e⟩ := hiter n z hz
    apply hn w hw
    have : z - p ^ n • w = a := by rw [e]; simp
    simpa [this] using ha
  rw [le_antisymm hZN hNZ]
  exact Submodule.fg_span (Set.finite_range v)
end UpperTheory
