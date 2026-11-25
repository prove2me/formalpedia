-- Prove2me | solution 1 for PositivityTheory.HtPt.KtwS.StepTwo.onW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:57:11.897414+00:00
-- url     : https://prove2.me/submissions/6bab6600-759e-4a8c-9836-a3e19a7b5b6c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_Development_WeilBound_CoreStatements_HodgeTatePoints_ExistsLineBundleTwistMulOf
import Theorems.Thm_PositivityTheory_HtPt_KtwS_exists_lineBundle_pow
import Theorems.Thm_PositivityTheory_HtPt_KtwS_exists_lineBundle_twistMulOf
import Theorems.Thm_PositivityTheory_HtPt_KtwS_exists_restrict_twistMul_pow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_mem_primeOf_of_isHomogeneous_ce26327b239d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.HtPt PositivityTheory.HtPt.KtwS
open GroundTheory.Heights₂.Heights.Kleiman MvPolynomial
noncomputable section
universe u v w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace PositivityTheory.HtPt.KtwS
namespace StepTwo
theorem _root_.solution (hLT : LineTwist.Statement.{u, w}) (hTA : TwistAlg.Statement.{u, w})
    (hRT : RestrictTwist.Statement.{u, w}) (hNR : NefRestrict.Statement.{u, w})
    (hJP : StepData.JProper.Statement.{u, w}) (hDrop : SubvarDrop.Statement.{u, w})
    (hPt : PrimeFiltration.Point.Statement.{u, w}) (hRes : PrimeFiltration.Restrict.Statement.{u, w})
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w}) (hTV : TwistVanish.Statement.{u, w})
    (T : StepData k x) (hK : ∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e)
    (pp : Ideal (Poly k N)) (hpr : pp.IsPrime) (hhom : ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp)
    (hle : primeOf (S := k) x ≤ pp) (hJ : ∀ (f : Poly k N) (e : ℕ), f ∈ T.J → f.IsHomogeneous e → f ∈ pp)
    (hrel : ∃ j, (X j : Poly k N) ∉ pp) :
    ∃ c₁ : ℤ, ∀ (b : ℕ) (Q : LineBundle k x), Q.toSubSystem = T.L.pow b → ∀ c : ℤ, c₁ ≤ c →
      Subsingleton (SubSystem.quotH (Q.twist (twistSys k x c))
        ((Q.twist (twistSys k x c)).twist (idealSys x pp)) 1) := by
  obtain ⟨j, hjp⟩ := hrel
  have hj : x j ≠ 0 := fun h0 => hjp (hle ((mem_primeOf_of_isHomogeneous x (isHomogeneous_X k j)).mpr
    (by rw [aeval_X]; exact h0)))
  obtain ⟨hcp, hpt⟩ := hPt k Ω N x pp hpr hhom hle j hj hjp

  have := hcp
  let A := chartRing k x (singleChart hj)
  let I : Ideal A := chartPrime pp hj
  let ψ : A →ₐ[k] I.ResidueField := IsScalarTower.toAlgHom k A I.ResidueField
  have hker : RingHom.ker ψ = I := Ideal.ker_algebraMap_residueField I
  have hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0 := by
    intro i h hx
    apply h
    have h0 : ratio (S := k) hj i = 0 := Subtype.ext (by change x i / x j = 0; rw [hx, zero_div])
    rw [h0, map_zero]
  have hpy : primeOf (S := k) (fun i => ψ (ratio hj i)) = pp := hpt _ ψ hker
  have hxy' : primeOf (S := k) x ≤ primeOf (S := k) (fun i => ψ (ratio hj i)) := hpy ▸ hle

  obtain ⟨f, e₀, hfJ, hfh, hfq⟩ := hJP k Ω N x T
  obtain ⟨e, he, hsub⟩ := hDrop k Ω N x T.d pp T.dim hpr hhom hle ⟨j, hjp⟩ ⟨f, hJ f e₀ hfJ hfh, hfq⟩
  have hsubW : IsSubvar (fun i => ψ (ratio hj i))
      (primeOf (S := k) (fun i => ψ (ratio hj i))) e := by
    rw [hpy]
    exact ⟨hsub.isPrime, hsub.homog, le_of_eq hpy, hsub.relevant, hsub.dim⟩

  obtain ⟨M', rM, hM'⟩ := hRes k Ω N x pp hpr hhom hle j hj hjp _ ψ hker hxy T.M
  have hRM : RestrictData T.M.toSubSystem hxy M'.toSubSystem rM :=
    ⟨fun I => (hM' I).1, fun I => (hM' I).2.1, fun I => (hM' I).2.2.1, fun I => (hM' I).2.2.2⟩
  have hnef : Nef M'.toSubSystem := hNR k Ω N x _ _ hxy hxy' T.M M' rM hRM T.nef

  have hts : 0 < T.t - T.s' := by
    have hd : (1 : ℚ) ≤ (T.d : ℚ) + 1 := by
      have := (Nat.cast_nonneg T.d : (0 : ℚ) ≤ T.d); linarith
    have ht : 0 < T.t := by
      by_contra hneg'
      have hneg : T.t ≤ 0 := not_lt.mp hneg'
      have : T.t / ((T.d : ℚ) + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg (by positivity)
      linarith [T.s'_pos, T.s'_lt]
    have : T.t / ((T.d : ℚ) + 1) ≤ T.t := div_le_self ht.le hd
    linarith [T.s'_lt]
  obtain ⟨q, m', hq, hm', hva⟩ := hK e he _ N _ M' hsubW hnef (T.t - T.s') hts
  obtain ⟨rr, h, hvb⟩ := hva
  have hqm : (q : ℤ) * T.m = T.p * m' := by
    have : (((q : ℤ) * T.m : ℤ) : ℚ) = ((T.p * m' : ℤ) : ℚ) := by
      push_cast; rw [T.m_eq, hm']; ring
    exact_mod_cast this

  obtain ⟨B, hB⟩ := exists_lineBundle_twistMulOf hLT M' q m'
  obtain ⟨L', hL'⟩ := exists_lineBundle_twistMulOf hLT M' T.p T.m
  have hv : ∀ b₂ : ℕ, ∃ c₀ : ℤ, ∀ (b' : ℕ) (c : ℤ), c₀ ≤ c →
      Subsingleton (((((twistMul M'.toSubSystem T.p T.m).pow b₂).twist
        ((twistMul M'.toSubSystem q m').pow b')).twist (twistSys k (fun i => ψ (ratio hj i)) c)).H 1) := by
    intro b₂
    obtain ⟨G, hG⟩ := exists_lineBundle_pow hLT L' b₂
    obtain ⟨c₀, hc₀⟩ := hTV k _ N _ G B rr h (fun l => by rw [hB]; exact hvb.mem_secs l)
      (fun I => by rw [hB]; exact hvb.generates I)
    refine ⟨c₀, fun b' c hc => ?_⟩
    have hs := hc₀ b' c hc
    rwa [hG, hL', hB] at hs
  choose cv hcv using hv
  refine ⟨∑ b₂ ∈ Finset.range q, |cv b₂|, fun b Q hQ c hc => ?_⟩
  obtain ⟨Qb, Qb', r', hQb, hQb', hrd⟩ :=
    exists_restrict_twistMul_pow hLT hRT hxy hxy' T.M M' rM hRM T.p T.m b
  obtain ⟨eqv⟩ := hRQ k Ω N x pp hpr hhom hle j hj hjp _ ψ hker hxy Qb Qb' r' hrd c 1
  have hQbQ : Qb.toSubSystem = Q.toSubSystem := by rw [hQb, hQ]; rfl
  have hW : Qb'.toSubSystem = ((twistMul M'.toSubSystem T.p T.m).pow (b % q)).twist
      ((twistMul M'.toSubSystem q m').pow (T.p * (b / q))) := by
    rw [hQb', ← hTA k _ N _ M'.toSubSystem T.p q T.m m' (b / q) (b % q) hqm, Nat.div_add_mod b q]
  have hlt : b % q < q := Nat.mod_lt b (by omega)
  have hcb : cv (b % q) ≤ c :=
    le_trans (le_abs_self _) (le_trans (Finset.single_le_sum (f := fun b₂ => |cv b₂|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hlt)) hc)
  have hs : Subsingleton ((Qb'.twist (twistSys k (fun i => ψ (ratio hj i)) c)).H 1) := by
    rw [hW]; exact hcv (b % q) (T.p * (b / q)) c hcb
  rw [← hQbQ]
  exact @Equiv.subsingleton _ _ eqv.toEquiv hs
end StepTwo
end PositivityTheory.HtPt.KtwS
