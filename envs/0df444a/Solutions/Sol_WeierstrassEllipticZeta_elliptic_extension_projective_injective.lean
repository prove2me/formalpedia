-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_extension_projective_injective
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T18:28:19.617886+00:00
-- url     : https://prove2.me/submissions/c301920b-1f4b-42e2-a7d3-8d403f3ebd7c

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_formula
import Theorems.Thm_WeierstrassEllipticZeta_sigma_addition_from_differential
import Mathlib.Tactic.LinearCombination

noncomputable section
open Filter TranscendenceTheory
open scoped Topology
open WeierstrassEllipticZeta

private theorem sigma_double_entire (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (hadd : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice →
      D.sigma (z + v) * D.sigma (z - v) =
        (L.weierstrassP v - L.weierstrassP z) * D.sigma z ^ 2 * D.sigma v ^ 2)
    (z : ℂ) (hz : z ∉ L.lattice) :
    D.sigma (2 * z) = -D.sigma z ^ 4 * L.derivWeierstrassP z := by
  have hP : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hz)).hasDerivAt
  have hplus := (D.entire (z + z)).hasDerivAt.comp z ((hasDerivAt_id z).const_add z)
  have hminus : HasDerivAt (fun v => D.sigma (z - v)) (-1) z := by
    have h : HasDerivAt D.sigma 1 (z - z) := by simpa using D.deriv_zero
    simpa [Function.comp_def] using! h.comp z ((hasDerivAt_id z).const_sub z)
  have hleft := hplus.mul hminus
  have hright := (((hP.sub_const (L.weierstrassP z)).mul_const (D.sigma z ^ 2)).mul
    ((D.hasDerivAt z hz).pow 2))
  have heq : (fun v => D.sigma (z + v) * D.sigma (z - v)) =ᶠ[𝓝 z]
      (fun v => (L.weierstrassP v - L.weierstrassP z) * D.sigma z ^ 2 * D.sigma v ^ 2) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with v hv
    exact hadd z v hz hv
  have hh := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  simp only [Function.comp_apply, Pi.pow_apply, sub_self, D.zero, mul_zero, zero_mul, zero_add,
    add_zero, ← two_mul] at hh
  linear_combination -hh

private theorem sigma_zero_iff_lattice (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → D.sigma z ≠ 0)
    (hadd : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice →
      D.sigma (z + v) * D.sigma (z - v) =
        (L.weierstrassP v - L.weierstrassP z) * D.sigma z ^ 2 * D.sigma v ^ 2)
    (z : ℂ) : D.sigma z = 0 ↔ z ∈ L.lattice := by
  constructor
  · intro hz
    by_contra h
    exact hne z h hz
  · intro hz
    let a : ℂ := L.ω₁ / 4
    have h2a : 2 * a ∉ L.lattice := by
      convert L.ω₁_div_two_notMem_lattice using 1
      dsimp [a]
      ring
    have ha : a ∉ L.lattice := by
      intro ha
      exact h2a (by simpa [two_mul] using L.lattice.add_mem ha ha)
    have hza : z - a ∉ L.lattice := by
      intro h
      exact ha (by simpa using L.lattice.sub_mem hz h)
    have hz2a : z - 2 * a ∉ L.lattice := by
      intro h
      exact h2a (by simpa using L.lattice.sub_mem hz h)
    have hp : L.weierstrassP (z - a) = L.weierstrassP a := by
      have hp := L.weierstrassP_add_coe (-a) ⟨z, hz⟩
      simpa [sub_eq_add_neg, add_comm] using hp
    have hh := hadd (z - a) a hza ha
    rw [hp, sub_self, zero_mul, zero_mul, sub_add_cancel] at hh
    have hsub : z - a - a = z - 2 * a := by ring
    rw [hsub] at hh
    exact (mul_eq_zero.mp hh).resolve_right (hne _ hz2a)

private theorem weierstrass_pair_separates (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (hne : ∀ z : ℂ, z ∉ L.lattice → D.sigma z ≠ 0)
    (hadd : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice →
      D.sigma (z + v) * D.sigma (z - v) =
        (L.weierstrassP v - L.weierstrassP z) * D.sigma z ^ 2 * D.sigma v ^ 2)
    (z w : ℂ) (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hp : L.weierstrassP z = L.weierstrassP w)
    (hd : L.derivWeierstrassP z = L.derivWeierstrassP w) : z - w ∈ L.lattice := by
  have hs := hadd z w hz hw
  rw [hp, sub_self, zero_mul, zero_mul] at hs
  rcases mul_eq_zero.mp hs with hs | hs
  · have hsum := (sigma_zero_iff_lattice L D hne hadd (z + w)).mp hs
    have hodd : L.derivWeierstrassP w = -L.derivWeierstrassP z := by
      have h := L.derivWeierstrassP_add_coe (-z) ⟨z + w, hsum⟩
      simpa using h
    have hd0 : L.derivWeierstrassP z = 0 := by linear_combination (hd + hodd) / 2
    have hs2 : D.sigma (2 * z) = 0 := by
      rw [sigma_double_entire L D hadd z hz, hd0, mul_zero]
    have h2 := (sigma_zero_iff_lattice L D hne hadd (2 * z)).mp hs2
    convert L.lattice.sub_mem h2 hsum using 1
    ring
  · exact (sigma_zero_iff_lattice L D hne hadd (z - w)).mp hs

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (P : GraphQuotientExtension L.lattice η → ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (hP : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (P ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)
    (F : ProjectiveExtensionFiberModel L.g₂ L.g₃)
    (hP_action : ∀ (u : ℂ) (e : GraphQuotientExtension L.lattice η),
      P (e + extensionInclusion L.lattice η u) = F.action u (P e)) :
    Function.Injective P := by
  obtain ⟨hne, hadd⟩ := sigma_addition_from_differential L D
    (hasDerivAt_weierstrassZeta L) (zeta_addition_formula L)
  have hS0 : S 0 = fun z => D.sigma z ^ 3 := by
    apply AnalyticOnNhd.eq_of_eventuallyEq (hS 0)
      (fun z _ => (D.entire.analyticAt z).pow 3) (z₀ := L.ω₁ / 2)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      L.ω₁_div_two_notMem_lattice] with z hz
    simpa using hS_value z hz 0
  have hS0_zero (z : ℂ) : S 0 z = 0 ↔ z ∈ L.lattice := by
    rw [hS0]
    simpa using sigma_zero_iff_lattice L D hne hadd z
  intro e f hef
  obtain ⟨⟨z, u⟩, rfl⟩ := (extensionPeriodGraph L.lattice η).mkQ_surjective e
  obtain ⟨⟨w, t⟩, rfl⟩ := (extensionPeriodGraph L.lattice η).mkQ_surjective f
  obtain ⟨hv, hval⟩ := hP z u
  obtain ⟨hv', hval'⟩ := hP w t
  have heq := congrArg (fun p : ProjectiveExtensionChartLocus L.g₂ L.g₃ => p.val.val) hef
  rw [hval, hval'] at heq
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp heq
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp [Units.smul_def] at h0 h1 h2
  have hzw : z - w ∈ L.lattice := by
    by_cases hz : z ∈ L.lattice
    · have hw : w ∈ L.lattice := by
        apply (hS0_zero w).mp
        have hzero : (c : ℂ) * S 0 w = 0 := h0.trans ((hS0_zero z).mpr hz)
        exact (mul_eq_zero.mp hzero).resolve_left c.ne_zero
      exact L.lattice.sub_mem hz hw
    · have hw : w ∉ L.lattice := by
        intro hw
        apply hz
        apply (hS0_zero z).mp
        rw [← h0, (hS0_zero w).mpr hw, mul_zero]
      have h0' : (c : ℂ) * D.sigma w ^ 3 = D.sigma z ^ 3 := by
        simpa [hS0] using h0
      have hp : L.weierstrassP z = L.weierstrassP w := by
        apply mul_left_cancel₀ (pow_ne_zero 3 (hne z hz))
        simp only [hS_value z hz 1, hS_value w hw 1, Matrix.cons_val_one,
          Matrix.cons_val_zero] at h1
        rw [← mul_assoc, h0'] at h1
        exact h1.symm
      have hd : L.derivWeierstrassP z = L.derivWeierstrassP w := by
        apply mul_left_cancel₀ (pow_ne_zero 3 (hne z hz))
        simp only [hS_value z hz 2, hS_value w hw 2] at h2
        rw [← mul_assoc, h0'] at h2
        exact h2.symm
      exact weierstrass_pair_separates L D hne hadd z w hz hw hp hd
  let ω : L.lattice := ⟨z - w, hzw⟩
  let v : ℂ := u - t + η ω
  have hvertical : (extensionPeriodGraph L.lattice η).mkQ (z, u) =
      (extensionPeriodGraph L.lattice η).mkQ (w, t) + extensionInclusion L.lattice η v := by
    change (extensionPeriodGraph L.lattice η).mkQ (z, u) =
      (extensionPeriodGraph L.lattice η).mkQ (w, t) +
        (extensionPeriodGraph L.lattice η).mkQ (0, v)
    rw [← map_add]
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨ω, ?_⟩
    apply Prod.ext
    · simp [ω]
    · change -(η ω) = u - (t + v)
      dsimp [v]
      ring
  have hfix : F.action v (P ((extensionPeriodGraph L.lattice η).mkQ (w, t))) =
      P ((extensionPeriodGraph L.lattice η).mkQ (w, t)) := by
    rw [← hP_action, ← hvertical]
    exact hef
  obtain ⟨v₀, hv₀, unique⟩ :=
    (F.fiber (P ((extensionPeriodGraph L.lattice η).mkQ (w, t))) _).mp rfl
  have hv0 : v = 0 := (unique v hfix).trans (unique 0 (F.zero_action _)).symm
  simpa [hv0] using hvertical

