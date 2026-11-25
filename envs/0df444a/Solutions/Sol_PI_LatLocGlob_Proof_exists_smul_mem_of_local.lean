-- Prove2me | solution 1 for PI.LatLocGlob.Proof.exists_smul_mem_of_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:52:21.030942+00:00
-- url     : https://prove2.me/submissions/610615e8-c9d6-4c1b-9f71-d981524ad25e

import Definitions.Def_Formalism_PeriodIntegrals_LatLocGlob
import Definitions.Def_Lemmata_GeneralBFactThirdBisAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalGlobalLattice_ExistsSmulMemOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LatLocGlob PI.LatLocGlob.Proof
open PI.LatLocGlob
variable {R V : Type} [CommRing R] [IsDedekindDomain R] [AddCommGroup V] [Module R V]
namespace PI.LatLocGlob.Proof
theorem _root_.solution (W : Ideal R → Set V) (L : Submodule R V)
    (hL : ∀ y, y ∈ L ↔ ∀ q : Ideal R, q.IsMaximal → y ∈ W q)
    (hWsmul : ∀ q : Ideal R, q.IsMaximal → ∀ (r : R) (y : V), y ∈ W q → r • y ∈ W q)
    (hWsat : ∀ q : Ideal R, q.IsMaximal → ∀ (u : R) (y : V), u ∉ q → u • y ∈ W q → y ∈ W q)
    {p : Ideal R} (hp : p.IsMaximal) {x : V} (hx : x ∈ W p) {d : R} (hd : d ≠ 0)
    (hdx : d • x ∈ L) : ∃ s : R, s ∉ p ∧ s • x ∈ L := by
  classical
  by_cases hdp : d ∈ p
  swap
  · exact ⟨d, hdp, hdx⟩
  have hpbot : p ≠ ⊥ := fun h => hd (by rw [h] at hdp; simpa using hdp)
  have hnf : ¬ IsField R := by
    rw [Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top]
    exact ⟨p, bot_lt_iff_ne_bot.2 hpbot, lt_top_iff_ne_top.2 hp.ne_top⟩
  let I : Ideal R := L.comap (LinearMap.toSpanSingleton R V x)
  have hI : ∀ r, r ∈ I ↔ r • x ∈ L := fun r => by simp [I]
  have hI0 : I ≠ ⊥ := by
    intro h
    have h1 := (hI d).2 hdx
    rw [h] at h1
    exact hd (by simpa using h1)
  obtain ⟨Z, hZle, hZne⟩ := PrimeSpectrum.exists_primeSpectrum_prod_le_and_ne_bot_of_domain hnf hI0
  have key : ∀ Y : Multiset (Ideal R), (∀ P ∈ Y, P.IsPrime ∧ P ≠ ⊥) →
      ∀ y ∈ W p, (∀ r ∈ Y.prod, r • y ∈ L) → ∃ s : R, s ∉ p ∧ s • y ∈ L := by
    intro Y
    induction Y using Multiset.induction_on with
    | empty =>
      intro _ y _ hy
      refine ⟨1, (Ideal.ne_top_iff_one p).1 hp.ne_top, hy 1 ?_⟩
      simp
    | cons P Y ih =>
      intro hPY y hyp hy
      have hP := hPY P (Multiset.mem_cons.2 (Or.inl rfl))
      have hPmax : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP.2 hP.1
      have hY' : ∀ Q ∈ Y, Q.IsPrime ∧ Q ≠ ⊥ := fun Q hQ => hPY Q (Multiset.mem_cons.2 (Or.inr hQ))
      rw [Multiset.prod_cons] at hy
      by_cases hPp : P = p
      · apply ih hY' y hyp
        intro r hr
        rw [hL]
        intro q hq
        by_cases hqp : q = p
        · rw [hqp]; exact hWsmul p hp r y hyp
        · obtain ⟨t, htP, htq⟩ : ∃ t ∈ P, t ∉ q := by
            by_contra h
            push Not at h
            exact hqp ((hPmax.eq_of_le hq.ne_top (fun t ht => h t ht)).symm.trans hPp)
          have h1 := (hL _).1 (hy (t * r) (Ideal.mul_mem_mul htP hr)) q hq
          rw [mul_smul] at h1
          exact hWsat q hq t _ htq h1
      · obtain ⟨a, haP, hap⟩ : ∃ a ∈ P, a ∉ p := by
          by_contra h
          push Not at h
          exact hPp (hPmax.eq_of_le hp.ne_top (fun t ht => h t ht))
        obtain ⟨s, hs, hsy⟩ := ih hY' (a • y) (hWsmul p hp a y hyp) (fun r hr => by
          have h1 := hy (a * r) (Ideal.mul_mem_mul haP hr)
          rwa [mul_comm, mul_smul] at h1)
        refine ⟨s * a, fun h => (hp.isPrime.mem_or_mem h).elim hs hap, ?_⟩
        rwa [mul_smul]
  apply key (Z.map PrimeSpectrum.asIdeal) _ x hx
  · intro r hr
    exact (hI r).1 (hZle hr)
  · intro P hP
    obtain ⟨P', _, rfl⟩ := Multiset.mem_map.1 hP
    refine ⟨P'.isPrime, fun h => hZne ?_⟩
    have h0 : (0 : Ideal R) ∈ Z.map PrimeSpectrum.asIdeal := by
      rw [Ideal.zero_eq_bot, ← h]; exact hP
    rw [← Ideal.zero_eq_bot]
    exact Multiset.prod_eq_zero h0
end PI.LatLocGlob.Proof
