-- Prove2me | solution 1 for ReciprocityTheory.Cheb.inertia_trivial_cyclotomic_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:39.310289+00:00
-- url     : https://prove2.me/submissions/66a59171-3395-4d05-a165-2bf709485618

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    [IsGalois E (CyclotomicField l E)]
    (P : Prm (CyclotomicField l E)) (hl : Nat.Coprime (Nrm P) l)
    (g : Gal(CyclotomicField l E/E)) (hg : g ∈ P.asIdeal.inertia Gal(CyclotomicField l E/E)) : g = 1 := by
  have hlp : l.Prime := Fact.out
  have : NeZero l := ⟨hlp.ne_zero⟩
  set M := CyclotomicField l E
  have hz0 := IsCyclotomicExtension.zeta_spec l E M
  have hz := hz0.toInteger_isPrimitiveRoot
  set ζ := hz0.toInteger
  have h1 : Ideal.absNorm P.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top
  have hq := hz.idealQuotient_mk (I := P.asIdeal) h1 hl
  have hgl : (g • ζ) ^ l = 1 := by rw [← smul_pow', hz.pow_eq_one, smul_one]
  obtain ⟨i, hi, hiz⟩ := hz.eq_pow_of_pow_eq_one hgl
  have hmem : g • ζ - ζ ∈ P.asIdeal := hg ζ
  rw [← hiz, ← Ideal.Quotient.eq, map_pow] at hmem
  have hi1 : i = 1 := hq.pow_inj hi hlp.one_lt (by rw [hmem, pow_one])
  rw [hi1, pow_one] at hiz
  have hfix : g (IsCyclotomicExtension.zeta l E M) = IsCyclotomicExtension.zeta l E M := by
    have := congrArg (fun x : 𝓞 M => (x : M)) hiz
    exact this.symm
  have hext : (g : M →ₐ[E] M) = AlgHom.id E M := by
    refine AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hz0) ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hfix
  ext x
  exact DFunLike.congr_fun hext x
end ReciprocityTheory.Cheb
