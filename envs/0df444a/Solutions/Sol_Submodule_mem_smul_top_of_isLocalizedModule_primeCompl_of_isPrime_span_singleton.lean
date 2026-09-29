-- Prove2me | solution 1 for Submodule.mem_smul_top_of_isLocalizedModule_primeCompl_of_isPrime_span_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/2ccc8d61-1f54-5610-8908-49c0028a7053

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Submodule_mem_smul_top_of_isLocalizedModule_primeCompl_of_isPrime_span_singleton

set_option autoImplicit false

open scoped Pointwise

theorem solution
    {A : Type*} [CommRing A] {M N : Type*} [AddCommGroup M] [Module A M] [Module.Projective A M]
    [AddCommGroup N] [Module A N]
    (ϖ : A) (hϖ : (Ideal.span {ϖ} : Ideal A).IsPrime)
    (𝔭 : Ideal A) [𝔭.IsPrime] (h𝔭 : ϖ ∈ 𝔭)
    (f : M →ₗ[A] N) [IsLocalizedModule 𝔭.primeCompl f]
    (m : M) (hm : f m ∈ ϖ • (⊤ : Submodule A N)) :
    m ∈ ϖ • (⊤ : Submodule A M) := by
  classical
  set S := 𝔭.primeCompl with hSdef

  obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm
  obtain ⟨⟨m', s⟩, hms⟩ := IsLocalizedModule.mk'_surjective S f y
  simp only [Function.uncurry_apply_pair] at hms
  have h1 : f ((s : A) • m) = f (ϖ • m') := by
    calc f ((s : A) • m) = (s : A) • f m := f.map_smul _ _
      _ = ϖ • ((s : A) • y) := by rw [← hy, smul_comm]
      _ = ϖ • (s • IsLocalizedModule.mk' f m' s) := by rw [hms]; rfl
      _ = ϖ • f m' := by rw [IsLocalizedModule.mk'_cancel']
      _ = f (ϖ • m') := (f.map_smul _ _).symm
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists S f).mp h1
  have hc' : (c : A) • (s : A) • m = (c : A) • ϖ • m' := hc
  set u : A := (c : A) * (s : A) with hu
  have huS : u ∈ S := S.mul_mem c.2 s.2
  have hum : u • m = ϖ • ((c : A) • m') := by
    rw [hu, mul_smul, hc', smul_comm]
  have huϖ : u ∉ (Ideal.span {ϖ} : Ideal A) := fun h =>
    huS ((Ideal.span_singleton_le_iff_mem 𝔭).mpr h𝔭 h)

  obtain ⟨sec, hsec⟩ := Module.Projective.out (R := A) (P := M)
  set v : M →₀ A := sec m with hv
  have hcoord : ∀ i, v i ∈ (Ideal.span {ϖ} : Ideal A) := by
    intro i
    have h2 : u * v i = ϖ * sec ((c : A) • m') i := by
      have := congrArg (fun w : M →₀ A => w i) (congrArg sec hum)
      simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using this
    have h3 : u * v i ∈ (Ideal.span {ϖ} : Ideal A) :=
      h2 ▸ Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)
    exact (hϖ.mem_or_mem h3).resolve_left huϖ

  have hdiv : ∀ i, ∃ b : A, ϖ * b = v i := fun i => by
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (hcoord i)
    exact ⟨b, by rw [mul_comm, hb]⟩
  choose b hb using hdiv
  set g : M →₀ A := Finsupp.onFinset v.support (fun i => if v i = 0 then 0 else b i) (by
    intro i hi
    rw [Finsupp.mem_support_iff]
    intro h0
    exact hi (if_pos h0)) with hg
  have hϖg : ϖ • g = v := by
    ext i
    rw [Finsupp.smul_apply, hg, Finsupp.onFinset_apply, smul_eq_mul]
    by_cases h0 : v i = 0
    · rw [if_pos h0, mul_zero, h0]
    · rw [if_neg h0, hb]

  have hm' : m = ϖ • Finsupp.linearCombination A id g := by
    rw [← map_smul, hϖg, hv]
    exact (hsec m).symm
  rw [hm']
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

end S_Submodule_mem_smul_top_of_isLocalizedModule_primeCompl_of_isPrime_span_singleton
end P2MW
export P2MW.S_Submodule_mem_smul_top_of_isLocalizedModule_primeCompl_of_isPrime_span_singleton (solution)
