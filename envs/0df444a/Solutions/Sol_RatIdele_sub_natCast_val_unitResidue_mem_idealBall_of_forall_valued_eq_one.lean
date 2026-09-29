-- Prove2me | solution 1 for RatIdele.sub_natCast_val_unitResidue_mem_idealBall_of_forall_valued_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/246f7d39-a5f1-527b-aa92-9aa676bf24fe

import Mathlib
import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RatIdele_sub_natCast_val_unitResidue_mem_idealBall_of_forall_valued_eq_one

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.AdelicLevel AdelicDock

namespace KRResidue

noncomputable section

theorem eq_padicPlace (w : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ (p : ℕ) (hp : p.Prime), w = @padicPlace p ⟨hp⟩ := by
  refine ⟨Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) w, Rat.HeightOneSpectrum.prime_natGenerator w, ?_⟩
  show w = (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm _
  exact ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply w).symm

theorem natGenerator_padicPlace (p : ℕ) [Fact p.Prime] :
    Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) (padicPlace p) = p :=
  congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, Fact.out⟩)

theorem equivPi_apply_eq_natCast_val {M : ℕ} (hM : M ≠ 0) (r : ZMod M) (q : M.primeFactors) :
    ZMod.equivPi M hM r q = ((r.val : ℕ) : ZMod ((q : ℕ) ^ M.factorization q)) := by
  haveI : NeZero M := ⟨hM⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val r, map_natCast]
  rfl

theorem ρ_finIncl_eq_one (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((u : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1) :
    RatIdele.ρ (Units.map (finIncl (𝓞 ℚ) ℚ) u) = 1 := by
  refine RatIdele.ρ_eq_of_isNormalizer ⟨fun v => ?_, ?_⟩
  · rw [map_one, Units.coe_map, finIncl_apply_snd]; exact hu v
  · rw [RatIdele.archCoord_finIncl, Rat.cast_one, mul_one]; exact one_pos

theorem unitAt_finIncl (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((u : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1) (v : HeightOneSpectrum (𝓞 ℚ)) :
    RatIdele.unitAt v (Units.map (finIncl (𝓞 ℚ) ℚ) u) = (u : FiniteAdeleRing (𝓞 ℚ) ℚ) v := by
  unfold RatIdele.unitAt
  rw [ρ_finIncl_eq_one u hu, map_one, inv_one, mul_one, Units.coe_map, finIncl_apply_snd]

theorem padicRingEquiv_unitPadicAt (p : ℕ) [hp : Fact p.Prime] (x : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    padicRingEquiv p ((RatIdele.unitPadicAt p x : ℤ_[p]) : ℚ_[p]) = RatIdele.unitAt (padicPlace p) x := by
  unfold RatIdele.unitPadicAt
  have h1 : (((PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) ⟨p, hp.out⟩).symm.toAlgEquiv.toRingEquiv
      (RatIdele.unitIntAt ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩) x) : ℤ_[p]) : ℚ_[p])
      = (Padic.adicCompletionEquiv (𝓞 ℚ) ⟨p, hp.out⟩).symm
          (RatIdele.unitIntAt ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩) x :
            ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp.out⟩).adicCompletion ℚ) :=
    PadicInt.coe_adicCompletionIntegersEquiv_symm_apply (R := 𝓞 ℚ) ⟨p, hp.out⟩ _
  rw [h1, padicRingEquiv_apply]
  show (Padic.adicCompletionEquiv (𝓞 ℚ) ⟨p, hp.out⟩) ((Padic.adicCompletionEquiv (𝓞 ℚ) ⟨p, hp.out⟩).symm _) = _
  rw [ContinuousAlgEquiv.apply_symm_apply, RatIdele.coe_unitIntAt]
  rfl

end

end KRResidue

open KRResidue in
theorem solution
    (M : ℕ) [NeZero M] (u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hu : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((u : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1) :
    (u : FiniteAdeleRing (𝓞 ℚ) ℚ)
        - ((RatIdele.unitResidue M (Units.map (NumberField.AdelicLevel.finIncl (𝓞 ℚ) ℚ) u)).val : FiniteAdeleRing (𝓞 ℚ) ℚ)
      ∈ NumberField.AdelicLevel.idealBall (𝓞 ℚ) ℚ (Ideal.span {((M : ℕ) : 𝓞 ℚ)}) := by
  classical
  have hM : M ≠ 0 := NeZero.ne M
  set x : (AdeleRing (𝓞 ℚ) ℚ)ˣ := Units.map (finIncl (𝓞 ℚ) ℚ) u with hx_def
  set r : ZMod M := RatIdele.unitResidue M x with hr_def
  intro w
  show Valued.v ((((u : FiniteAdeleRing (𝓞 ℚ) ℚ) - ((r.val : ℕ) : FiniteAdeleRing (𝓞 ℚ) ℚ)) : FiniteAdeleRing (𝓞 ℚ) ℚ) w)
    ≤ idealBound (𝓞 ℚ) (Ideal.span {((M : ℕ) : 𝓞 ℚ)}) w
  have hsub : (((u : FiniteAdeleRing (𝓞 ℚ) ℚ) - ((r.val : ℕ) : FiniteAdeleRing (𝓞 ℚ) ℚ)) : FiniteAdeleRing (𝓞 ℚ) ℚ) w
      = (u : FiniteAdeleRing (𝓞 ℚ) ℚ) w - ((r.val : ℕ) : w.adicCompletion ℚ) := by
    rw [coe_sub_apply, ← finAdeleEval_apply (𝓞 ℚ) ℚ w ((r.val : ℕ) : FiniteAdeleRing (𝓞 ℚ) ℚ), map_natCast]
  rw [hsub]
  obtain ⟨p, hp, rfl⟩ := eq_padicPlace w
  haveI : Fact p.Prime := ⟨hp⟩
  have hspan : Ideal.span {((M : ℕ) : 𝓞 ℚ)} = ratLevel M := rfl
  by_cases hpM : p ∣ M
  ·
    have hy : padicRingEquiv p ((RatIdele.unitPadicAt p x : ℤ_[p]) : ℚ_[p]) = (u : FiniteAdeleRing (𝓞 ℚ) ℚ) (padicPlace p) := by
      rw [padicRingEquiv_unitPadicAt, hx_def, unitAt_finIncl u hu]
    have hrew : (u : FiniteAdeleRing (𝓞 ℚ) ℚ) (padicPlace p) - ((r.val : ℕ) : (padicPlace p).adicCompletion ℚ)
        = padicRingEquiv p (((RatIdele.unitPadicAt p x - ((r.val : ℕ) : ℤ_[p]) : ℤ_[p]) : ℚ_[p])) := by
      rw [PadicInt.coe_sub, map_sub, hy, PadicInt.coe_natCast, map_natCast]
    rw [hrew, hspan, valued_coe_le_idealBound_iff p hM, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
      map_natCast, sub_eq_zero]

    let q : M.primeFactors := ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpM, hM⟩⟩
    have h1 : PadicInt.toZModPow (M.factorization p) (RatIdele.unitPadicAt p x) = RatIdele.unitResidues M x q := rfl
    rw [h1, ← RatIdele.equivPi_unitResidue, ← hr_def]
    exact equivPi_apply_eq_natCast_val hM r q
  ·
    have hndvd : ¬ (padicPlace p).asIdeal ∣ Ideal.span {((M : ℕ) : 𝓞 ℚ)} := by
      rw [Ideal.dvd_span_singleton, RatIdele.natCast_mem_asIdeal_iff, natGenerator_padicPlace]
      exact hpM
    have hne : Ideal.span {((M : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hM
    rw [idealBound_eq_one_of_not_dvd hne hndvd]
    refine (Valuation.map_sub _ _ _).trans (max_le (hu _).le ?_)
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (natCast_mem _ _)

end S_RatIdele_sub_natCast_val_unitResidue_mem_idealBall_of_forall_valued_eq_one
end P2MW
export P2MW.S_RatIdele_sub_natCast_val_unitResidue_mem_idealBall_of_forall_valued_eq_one (solution)
