-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_extension_projective_descent
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T16:39:28.041003+00:00
-- url     : https://prove2.me/submissions/7d53ecf6-4830-4775-ac66-ec850f0a7d92

import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Theorems.Thm_WeierstrassEllipticZeta_weierstrassZeta_add_period
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

noncomputable section
open Filter Set TranscendenceTheory
open scoped Topology
open WeierstrassEllipticZeta

private lemma sigma_translation_factor (L : PeriodPair) (S : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → S.sigma z ≠ 0)
    (hzeta : ∀ ω z : ℂ, ω ∈ L.lattice → z ∉ L.lattice →
      weierstrassZeta L (z + ω) = weierstrassZeta L z + zetaQuasiPeriod L ω)
    (ω : ℂ) (hω : ω ∈ L.lattice) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z : ℂ, S.sigma (z + ω) =
      c * Complex.exp (zetaQuasiPeriod L ω * z) * S.sigma z := by
  let η := zetaQuasiPeriod L ω
  have hshift (z : ℂ) (hz : z ∉ L.lattice) : z + ω ∉ L.lattice := by
    intro h
    exact hz (by simpa using L.lattice.sub_mem h hω)
  have hd (z : ℂ) (hz : z ∉ L.lattice) :
      HasDerivAt (fun w => S.sigma (w + ω) / S.sigma w * Complex.exp (-η * w)) 0 z := by
    have h1 : HasDerivAt (fun w => S.sigma (w + ω))
        ((weierstrassZeta L z + η) * S.sigma (z + ω)) z := by
      simpa [hzeta ω z hω hz, η] using!
        (S.hasDerivAt (z + ω) (hshift z hz)).comp z ((hasDerivAt_id z).add_const ω)
    have h2 := ((hasDerivAt_id z).const_mul (-η)).cexp
    convert! ((h1.div (S.hasDerivAt z hz) (hne z hz)).mul h2) using 1
    simp only [Pi.div_apply, id_eq]
    field_simp
    ring
  obtain ⟨c, hc⟩ := L.isClosed_lattice.isOpen_compl.exists_is_const_of_deriv_eq_zero
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv)
  have heq (z : ℂ) (hz : z ∉ L.lattice) :
      S.sigma (z + ω) = c * Complex.exp (η * z) * S.sigma z := by
    have h := congrArg (fun w : ℂ => w * Complex.exp (η * z) * S.sigma z) (hc z hz)
    simpa [mul_assoc, ← Complex.exp_add, hne z hz] using h
  let u := L.ω₁ / 2
  have hu : u ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have hc0 : c ≠ 0 := by
    intro hc0
    have h := heq u hu
    simp only [hc0, zero_mul] at h
    exact hne (u + ω) (hshift u hu) h
  have hall : (fun z => S.sigma (z + ω)) =
      (fun z => c * Complex.exp (η * z) * S.sigma z) := by
    apply AnalyticOnNhd.eq_of_eventuallyEq
      (show AnalyticOnNhd ℂ (fun z => S.sigma (z + ω)) Set.univ from
        fun z _ => (S.entire.analyticAt (z + ω)).comp (f := fun w : ℂ => w + ω) (x := z)
          (analyticAt_id.add analyticAt_const))
      (show AnalyticOnNhd ℂ (fun z => c * Complex.exp (η * z) * S.sigma z) Set.univ from
        fun z _ => ((analyticAt_const.mul
          (analyticAt_const.mul analyticAt_id).cexp).mul (S.entire.analyticAt z)))
      (z₀ := u)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hu] with z hz
    exact heq z hz
  exact ⟨c, hc0, fun z => congrFun hall z⟩

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω) :
    ∃ P : GraphQuotientExtension L.lattice η → Projectivization ℂ (Fin 5 → ℂ),
      (∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        P ((extensionPeriodGraph L.lattice η).mkQ (z, u)) = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv) ∧
      (∀ (z : ℂ) (j : Fin 5),
        (P ((extensionCurve L.lattice η z).2)).rep j ≠ 0 ↔ S j z ≠ 0) ∧
      (∀ (z : ℂ) (i j : Fin 5),
        (P ((extensionCurve L.lattice η z).2)).rep i /
          (P ((extensionCurve L.lattice η z).2)).rep j = S i z / S j z) := by
  let V (z u : ℂ) : Fin 5 → ℂ :=
    ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z]
  have hV (z u : ℂ) : V z u ≠ 0 := by
    intro hz
    have h0 : S 0 z = 0 := by simpa [V] using congrFun hz 0
    have h2 : S 2 z = 0 := by simpa [V] using congrFun hz 2
    obtain ⟨j, hj⟩ := hS_ne z
    apply hj
    have hj' := congrFun hz j
    fin_cases j
    · exact h0
    · simpa [V] using hj'
    · exact h2
    · simpa [V, h0] using hj'
    · simpa [V, h2] using hj'
  have hV_zero (z : ℂ) : V z 0 = fun j => S j z := by
    ext j
    fin_cases j <;> simp [V]
  have hVa (u : ℂ) (j : Fin 5) : AnalyticOnNhd ℂ (fun z => V z u j) Set.univ := by
    intro z _
    have hs (i : Fin 5) := hS i z (Set.mem_univ z)
    fin_cases j
    · exact hs 0
    · exact hs 1
    · exact hs 2
    · exact (hs 3).add (analyticAt_const.mul (hs 0))
    · exact (hs 4).add (analyticAt_const.mul (hs 2))
  have hσne (z : ℂ) (hz : z ∉ L.lattice) : D.sigma z ≠ 0 := by
    intro hzero
    obtain ⟨j, hj⟩ := hS_ne z
    exact hj (by simp [hS_value z hz j, hzero])
  have hperiod (ω : L.lattice) (u : ℂ) :
      ∃ c : ℂ, c ≠ 0 ∧ ∀ z : ℂ,
        V (z + ω) (u - η ω) = (c * Complex.exp (η ω * z)) ^ 3 • V z u := by
    obtain ⟨c, hc, hσ⟩ := sigma_translation_factor L D hσne
      (weierstrassZeta_add_period L) ω ω.property
    refine ⟨c, hc, fun z => ?_⟩
    ext j
    have hall : (fun w : ℂ => V (w + ω) (u - η ω) j) =
        (fun w : ℂ => (c * Complex.exp (η ω * w)) ^ 3 * V w u j) := by
      apply AnalyticOnNhd.eq_of_eventuallyEq
        (show AnalyticOnNhd ℂ (fun w : ℂ => V (w + ω) (u - η ω) j) Set.univ from
          fun w _ => (hVa (u - η ω) j (w + ω) (Set.mem_univ _)).comp
            (f := fun x : ℂ => x + ω) (x := w) (analyticAt_id.add analyticAt_const))
        (show AnalyticOnNhd ℂ
            (fun w : ℂ => (c * Complex.exp (η ω * w)) ^ 3 * V w u j) Set.univ from
          fun w _ => ((analyticAt_const.mul
            (analyticAt_const.mul analyticAt_id).cexp).pow 3).mul
              (hVa u j w (Set.mem_univ _)))
        (z₀ := L.ω₁ / 2)
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
        L.ω₁_div_two_notMem_lattice] with w hw
      have hw' : w + ω ∉ L.lattice := by
        intro h
        exact hw (by simpa using L.lattice.sub_mem h ω.property)
      fin_cases j <;> simp [V, hS_value w hw, hS_value (w + ω) hw', hσ w,
        L.weierstrassP_add_coe w ω, L.derivWeierstrassP_add_coe w ω,
        weierstrassZeta_add_period L ω w ω.property hw, hη ω] <;> ring
    exact congrFun hall z
  let f (p : ℂ × ℂ) := Projectivization.mk ℂ (V p.1 p.2) (hV p.1 p.2)
  have hf (a b : ℂ × ℂ) (hab : a - b ∈ extensionPeriodGraph L.lattice η) :
      f a = f b := by
    obtain ⟨ω, hω⟩ := hab
    have h1 : (ω : ℂ) = a.1 - b.1 := congrArg Prod.fst hω
    have h2 : -η ω = a.2 - b.2 := congrArg Prod.snd hω
    have ha : a.1 = b.1 + ω := by linear_combination -h1
    have hb : a.2 = b.2 - η ω := by linear_combination -h2
    obtain ⟨c, _, hc⟩ := hperiod ω b.2
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨(c * Complex.exp (η ω * b.1)) ^ 3, ?_⟩
    rw [ha, hb, hc]
  let P : GraphQuotientExtension L.lattice η → Projectivization ℂ (Fin 5 → ℂ) :=
    Quotient.lift f (fun a b h => hf a b ((Submodule.quotientRel_def _).mp h))
  have hP (z u : ℂ) : P ((extensionPeriodGraph L.lattice η).mkQ (z, u)) =
      Projectivization.mk ℂ (V z u) (hV z u) := rfl
  have hrep (z : ℂ) : ∃ c : ℂ, c ≠ 0 ∧
      (P ((extensionCurve L.lattice η z).2)).rep = fun j => c * S j z := by
    change ∃ c : ℂ, c ≠ 0 ∧
      (P ((extensionPeriodGraph L.lattice η).mkQ (z, 0))).rep = _
    rw [hP]
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ (V z 0) (hV z 0)
    refine ⟨c, c.ne_zero, ?_⟩
    rw [← hc, hV_zero]
    rfl
  refine ⟨P, fun z u => ⟨hV z u, hP z u⟩, ?_, ?_⟩
  · intro z j
    obtain ⟨c, hc, h⟩ := hrep z
    rw [h]
    exact mul_ne_zero_iff.trans (and_iff_right hc)
  · intro z i j
    obtain ⟨c, hc, h⟩ := hrep z
    rw [h]
    exact mul_div_mul_left _ _ hc

