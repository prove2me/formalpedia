-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_extension_projective_surjective
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T18:54:38.70339+00:00
-- url     : https://prove2.me/submissions/de48696d-c6aa-488e-9537-0ecb646944d6

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

noncomputable section
open Filter TranscendenceTheory
open scoped Topology
open WeierstrassEllipticZeta

private theorem weierstrassP_takes_every_value (L : PeriodPair) (a : ℂ) :
    ∃ z : ℂ, z ∉ L.lattice ∧ L.weierstrassP z = a := by
  classical
  by_contra h
  have homit : ∀ z : ℂ, z ∉ L.lattice → L.weierstrassP z ≠ a := by
    simpa only [not_exists, not_and] using h
  let f : ℂ → ℂ := fun z => if z ∈ L.lattice then 0 else (L.weierstrassP z - a)⁻¹
  have hper (z : ℂ) (ω : L.lattice) : f (z + ω) = f z := by
    have hm : z + (ω : ℂ) ∈ L.lattice ↔ z ∈ L.lattice := by
      constructor
      · intro hh
        simpa using L.lattice.sub_mem hh ω.property
      · exact fun hh => L.lattice.add_mem hh ω.property
    simp [f, hm]
  have hzero : AnalyticAt ℂ f 0 := by
    let g : ℂ → ℂ := fun z => 1 + z ^ 2 * (L.weierstrassPExcept 0 z - a)
    have hg : AnalyticAt ℂ g 0 := analyticAt_const.add
      ((analyticAt_id.pow 2).mul ((L.analyticAt_weierstrassPExcept 0).sub analyticAt_const))
    have hg0 : g 0 ≠ 0 := by simp [g]
    have han := (analyticAt_id.pow 2).div hg hg0
    apply han.congr
    filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
    by_cases hz0 : z = 0
    · simp [hz0, g, f]
    · have hzL : z ∉ L.lattice := by
        intro hzL
        exact hz ⟨hzL, hz0⟩
      have hrel := L.ite_eq_one_sub_sq_mul_weierstrassP 0 L.lattice.zero_mem z
      have hden : g z = z ^ 2 * (L.weierstrassP z - a) := by
        simp only [hz0, if_false, sub_zero, zero_pow (by decide : 2 ≠ 0), div_zero,
          sub_zero] at hrel
        dsimp [g]
        linear_combination -hrel
      change z ^ 2 / g z = f z
      rw [hden]
      simp only [f, if_neg hzL]
      field_simp [hz0, sub_ne_zero.mpr (homit z hzL)]
  have hf : Differentiable ℂ f := by
    intro z
    by_cases hz : z ∈ L.lattice
    · have ha : AnalyticAt ℂ f (z - z) := by simpa using hzero
      have ht := ha.comp (f := fun w : ℂ => w - z) (analyticAt_id.sub analyticAt_const)
      have heq : (fun w : ℂ => f (w - z)) = f := by
        funext w
        simpa using (hper (w - z) ⟨z, hz⟩).symm
      simpa only [Function.comp_def, heq] using ht.differentiableAt
    · have ha := ((L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const).inv
        (sub_ne_zero.mpr (homit z hz))
      apply (ha.congr ?_).differentiableAt
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
      change w ∉ L.lattice at hw
      simp [f, hw]
  have hb := (IsZLattice.isCompact_range_of_periodic L.lattice f hf.continuous
    (fun z ω hω => hper z ⟨ω, hω⟩)).isBounded
  have hc := hf.apply_eq_apply_of_bounded hb (L.ω₁ / 2) 0
  apply homit (L.ω₁ / 2) L.ω₁_div_two_notMem_lattice
  apply sub_eq_zero.mp
  simpa [f, L.ω₁_div_two_notMem_lattice] using hc

private theorem weierstrass_pair_covers_affine (L : PeriodPair) (x y : ℂ)
    (hxy : y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃) :
    ∃ z : ℂ, z ∉ L.lattice ∧ L.weierstrassP z = x ∧ L.derivWeierstrassP z = y := by
  obtain ⟨z, hz, hx⟩ := weierstrassP_takes_every_value L x
  have hsq : L.derivWeierstrassP z ^ 2 = y ^ 2 := by
    rw [L.derivWeierstrassP_sq z hz, hx, hxy]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with hy | hy
  · exact ⟨z, hz, hx, hy⟩
  · refine ⟨-z, ?_, ?_, ?_⟩
    · intro h
      exact hz (by simpa using L.lattice.neg_mem h)
    · simpa using hx
    · rw [L.derivWeierstrassP_neg, hy, neg_neg]

private theorem projection_of_vector {g₂ g₃ : ℂ} (F : ProjectiveExtensionFiberModel g₂ g₃)
    (p : ProjectiveExtensionChartLocus g₂ g₃) (v : Fin 5 → ℂ) (hv : v ≠ 0)
    (heq : p.val.val = Projectivization.mk ℂ v hv) (hb : extensionBaseVector v ≠ 0) :
    F.projection p = Projectivization.mk ℂ (extensionBaseVector v) hb := by
  obtain ⟨hp, hproj⟩ := F.projection_coords p
  simp only [extensionProjectivePoint] at hp hproj
  rw [hproj]
  obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ v hv
  apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
  refine ⟨c, ?_⟩
  rw [heq, ← hc]
  ext i
  fin_cases i <;> simp [extensionBaseVector, Units.smul_def]

private theorem projection_infinity {g₂ g₃ : ℂ} (F : ProjectiveExtensionFiberModel g₂ g₃)
    (p q : ProjectiveExtensionChartLocus g₂ g₃)
    (hp0 : p.val.val.rep 0 = 0) (hq0 : q.val.val.rep 0 = 0) :
    F.projection p = F.projection q := by
  have hp1 : p.val.val.rep 1 = 0 := by
    have h := p.val.property.2
    simpa [extensionCubic, hp0] using h
  have hq1 : q.val.val.rep 1 = 0 := by
    have h := q.val.property.2
    simpa [extensionCubic, hq0] using h
  have hq2 : q.val.val.rep 2 ≠ 0 := q.property.resolve_left (not_not.mpr hq0)
  obtain ⟨hp, hproj⟩ := F.projection_coords p
  obtain ⟨hq, hproj'⟩ := F.projection_coords q
  simp only [extensionProjectivePoint] at hp hproj hq hproj'
  rw [hproj, hproj']
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨p.val.val.rep 2 / q.val.val.rep 2, ?_⟩
  ext i
  fin_cases i <;> simp [extensionBaseVector, hp0, hp1, hq0, hq1, hq2]

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
    (P : GraphQuotientExtension L.lattice η → ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (hP : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (P ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)
    (F : ProjectiveExtensionFiberModel L.g₂ L.g₃)
    (hP_action : ∀ (u : ℂ) (e : GraphQuotientExtension L.lattice η),
      P (e + extensionInclusion L.lattice η u) = F.action u (P e)) :
    Function.Surjective P := by
  have hS0 : S 0 = fun z => D.sigma z ^ 3 := by
    apply AnalyticOnNhd.eq_of_eventuallyEq (hS 0)
      (fun z _ => (D.entire.analyticAt z).pow 3) (z₀ := L.ω₁ / 2)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      L.ω₁_div_two_notMem_lattice] with z hz
    simpa using hS_value z hz 0
  intro q
  suffices ∃ e, F.projection (P e) = F.projection q by
    obtain ⟨e, he⟩ := this
    obtain ⟨u, hu, _⟩ := (F.fiber (P e) q).mp he
    exact ⟨e + extensionInclusion L.lattice η u, (hP_action u e).trans hu⟩
  by_cases hq0 : q.val.val.rep 0 = 0
  · let e := (extensionPeriodGraph L.lattice η).mkQ (0, 0)
    refine ⟨e, projection_infinity F (P e) q ?_ hq0⟩
    obtain ⟨hv, hval⟩ := hP 0 0
    obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep ℂ _ hv
    change (P ((extensionPeriodGraph L.lattice η).mkQ (0, 0))).val.val.rep 0 = 0
    rw [hval, ← hc]
    simp [hS0, D.zero]
  · let x : ℂ := q.val.val.rep 1 / q.val.val.rep 0
    let y : ℂ := q.val.val.rep 2 / q.val.val.rep 0
    have hxy : y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ := by
      have h := q.val.property.2
      simp [extensionCubic] at h
      dsimp [x, y]
      field_simp
      linear_combination h
    obtain ⟨z, hz, hx, hy⟩ := weierstrass_pair_covers_affine L x y hxy
    have hσ : D.sigma z ≠ 0 := by
      intro hσ
      obtain ⟨j, hj⟩ := hS_ne z
      rw [hS_value z hz j, hσ, zero_pow (by decide : 3 ≠ 0), zero_mul] at hj
      exact hj rfl
    let e := (extensionPeriodGraph L.lattice η).mkQ (z, 0)
    obtain ⟨hv, hval⟩ := hP z 0
    have hb : extensionBaseVector
        ![S 0 z, S 1 z, S 2 z, S 3 z + 0 * S 0 z, S 4 z + 0 * S 2 z] ≠ 0 := by
      intro hh
      have h := congrFun hh 0
      simp [extensionBaseVector, hS0, hσ] at h
    refine ⟨e, ?_⟩
    rw [projection_of_vector F (P e) _ hv hval hb]
    obtain ⟨hq, hproj⟩ := F.projection_coords q
    simp only [extensionProjectivePoint] at hq hproj
    rw [hproj]
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨D.sigma z ^ 3 / q.val.val.rep 0, ?_⟩
    ext i
    fin_cases i
    · simp [extensionBaseVector, hS0, hq0]
    · simp [extensionBaseVector, hS_value z hz 1, hx, x]
      ring
    · simp [extensionBaseVector, hS_value z hz 2, hy, y]
      ring

