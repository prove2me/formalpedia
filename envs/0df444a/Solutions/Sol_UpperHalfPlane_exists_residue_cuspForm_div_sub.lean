-- Prove2me | solution 1 for UpperHalfPlane.exists_residue_cuspForm_div_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1761da60-310a-521e-a361-a2193bc229f2

import Mathlib
import Theorems.Thm_UpperHalfPlane_sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UpperHalfPlane_exists_residue_cuspForm_div_sub

set_option autoImplicit false
set_option maxHeartbeats 6400000

open UpperHalfPlane ModularForm
open scoped MatrixGroups Topology ModularForm Manifold

private lemma cfad_resUnique {a c c' : ℂ} {om g g' : ℂ → ℂ}
    (hg : AnalyticAt ℂ g a) (hg' : AnalyticAt ℂ g' a)
    (h1 : ∀ᶠ z in 𝓝[≠] a, om z = c / (z - a) + g z)
    (h2 : ∀ᶠ z in 𝓝[≠] a, om z = c' / (z - a) + g' z) : c = c' := by
  have key : ∀ (d : ℂ) (u : ℂ → ℂ), AnalyticAt ℂ u a →
      (∀ᶠ z in 𝓝[≠] a, om z = d / (z - a) + u z) →
      Filter.Tendsto (fun z => (z - a) * om z) (𝓝[≠] a) (𝓝 d) := by
    intro d u hu hev
    have hsub : Filter.Tendsto (fun z : ℂ => z - a) (𝓝 a) (𝓝 0) := by
      simpa using ((continuous_id.fun_sub continuous_const).tendsto a :
        Filter.Tendsto (fun z : ℂ => z - a) (𝓝 a) (𝓝 (a - a)))
    have h0 : Filter.Tendsto (fun z : ℂ => d + (z - a) * u z) (𝓝 a) (𝓝 (d + 0 * u a)) :=
      tendsto_const_nhds.add (hsub.mul hu.continuousAt)
    have h1 : Filter.Tendsto (fun z : ℂ => d + (z - a) * u z) (𝓝[≠] a) (𝓝 d) := by
      simpa using h0.mono_left nhdsWithin_le_nhds
    refine h1.congr' ?_
    filter_upwards [hev, self_mem_nhdsWithin] with z hz (hzne : z ≠ a)
    rw [hz]
    field_simp [sub_ne_zero.mpr hzne]
  exact tendsto_nhds_unique (key c g hg h1) (key c' g' hg' h2)

private lemma cfad_dslope_analytic {u : ℂ → ℂ} {x : ℂ} (h : AnalyticAt ℂ u x) :
    AnalyticAt ℂ (dslope u x) x := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q.fslope, hq.has_fpower_series_dslope_fslope⟩

private lemma cfad_resTransport {om : ℂ → ℂ} {a b c : ℂ} {g M : ℂ → ℂ}
    (hg : AnalyticAt ℂ g a) (hexp : ∀ᶠ z in 𝓝[≠] a, om z = c / (z - a) + g z)
    (hM : AnalyticAt ℂ M b) (hMb : M b = a) (hM' : deriv M b ≠ 0) :
    ∃ g2 : ℂ → ℂ, AnalyticAt ℂ g2 b ∧
      ∀ᶠ w in 𝓝[≠] b, om (M w) * deriv M w = c / (w - b) + g2 w := by
  have hds : AnalyticAt ℂ (dslope M b) b := cfad_dslope_analytic hM
  have hds_b : dslope M b b = deriv M b := dslope_same M b
  have hdsne : ∀ᶠ w in 𝓝 b, dslope M b w ≠ 0 :=
    hds.continuousAt.eventually_ne (hds_b ▸ hM')
  have hMsub : ∀ᶠ w in 𝓝[≠] b, M w - a = (w - b) * dslope M b w := by
    filter_upwards [self_mem_nhdsWithin] with w (hw : w ≠ b)
    rw [dslope_of_ne M hw, slope_def_field, ← hMb]
    rw [mul_comm, div_mul_cancel₀ _ (sub_ne_zero.mpr hw)]
  have hMne : ∀ᶠ w in 𝓝[≠] b, M w ≠ a := by
    filter_upwards [hMsub, hdsne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with w hsub hne (hwb : w ≠ b) hMa
    rcases mul_eq_zero.mp (hsub.symm.trans (sub_eq_zero.mpr hMa)) with h | h
    · exact hwb (sub_eq_zero.mp h)
    · exact hne h
  have hMten : Filter.Tendsto M (𝓝[≠] b) (𝓝[≠] a) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, by filter_upwards [hMne] with w hw; simpa using hw⟩
    have := hM.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {b}ᶜ))
    rwa [hMb] at this
  have hexp' : ∀ᶠ w in 𝓝[≠] b, om (M w) = c / (M w - a) + g (M w) := hMten.eventually hexp
  have hqan : AnalyticAt ℂ (fun u => deriv M u / dslope M b u) b :=
    hM.deriv.div hds (hds_b ▸ hM')
  have hgM : AnalyticAt ℂ (fun w => g (M w)) b := by
    have : AnalyticAt ℂ g (M b) := hMb ▸ hg
    exact this.comp hM
  refine ⟨fun w => c * dslope (fun u => deriv M u / dslope M b u) b w + g (M w) * deriv M w,
    (analyticAt_const.mul (cfad_dslope_analytic hqan)).add (hgM.mul hM.deriv), ?_⟩
  have hq_b : deriv M b / dslope M b b = 1 := by
    rw [hds_b, div_self hM']
  filter_upwards [hexp', hMsub, hdsne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with w hom hsub hne (hwb : w ≠ b)
  rw [hom, dslope_of_ne _ hwb, slope_def_field, hq_b, hsub]
  have hwb' : w - b ≠ 0 := sub_ne_zero.mpr hwb
  field_simp
  ring

private lemma cfad_exists_expansion {fh Ft : ℂ → ℂ} {a : ℂ}
    (hfa : AnalyticAt ℂ fh a) (hFm : MeromorphicAt Ft a)
    (hs : meromorphicOrderAt Ft a ≤ 1) :
    ∃ p : ℂ × (ℂ → ℂ), AnalyticAt ℂ p.2 a ∧
      (p.1 ≠ 0 → 0 < meromorphicOrderAt Ft a) ∧
      ∀ᶠ z in 𝓝[≠] a, fh z / Ft z = p.1 / (z - a) + p.2 z := by
  have hne_top : meromorphicOrderAt Ft a ≠ ⊤ := by
    intro h
    rw [h] at hs
    exact absurd hs (by simp)
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hne_top
  obtain ⟨ψ, hψan, hψ0, hfac⟩ := (meromorphicOrderAt_eq_int_iff hFm).mp hd.symm
  have hψne : ∀ᶠ z in 𝓝 a, ψ z ≠ 0 := hψan.continuousAt.eventually_ne hψ0
  have hdle : d ≤ 1 := by
    have : (d : WithTop ℤ) ≤ (1 : ℤ) := hd ▸ hs
    exact_mod_cast this
  by_cases hd1 : d = 1
  · subst hd1
    refine ⟨(fh a / ψ a, dslope (fun z => fh z / ψ z) a),
      cfad_dslope_analytic (hfa.div hψan hψ0), fun _ => ?_, ?_⟩
    · rw [← hd]
      exact_mod_cast zero_lt_one
    · filter_upwards [hfac, hψne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
        with z hz hne (hza : z ≠ a)
      rw [hz, dslope_of_ne _ hza, slope_def_field]
      have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
      rw [zpow_one, smul_eq_mul]
      field_simp
      ring
  · have hd0 : d ≤ 0 := by omega
    obtain ⟨n, hn⟩ : ∃ n : ℕ, d = -(n : ℤ) :=
      ⟨(-d).toNat, by omega⟩
    refine ⟨(0, fun z => fh z * (z - a) ^ n / ψ z),
      (hfa.mul ((analyticAt_id.sub analyticAt_const).pow n)).div hψan hψ0,
      fun h => absurd rfl h, ?_⟩
    filter_upwards [hfac, hψne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with z hz hne (hza : z ≠ a)
    have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
    rw [hz, smul_eq_mul, hn, zpow_neg, zpow_natCast, zero_div, zero_add]
    field_simp

private lemma cfad_det_one (γ : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ) γ).val.det = 1 := by
  have h : ((Matrix.SpecialLinearGroup.mapGL ℝ) γ).val
      = ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ : Matrix (Fin 2) (Fin 2) ℝ) := rfl
  rw [h, Matrix.SpecialLinearGroup.det_coe]

private lemma cfad_det_pos (γ : SL(2, ℤ)) :
    0 < ((Matrix.SpecialLinearGroup.mapGL ℝ) γ).val.det := by
  rw [cfad_det_one]; norm_num

private noncomputable def cfad_mob (γ : SL(2, ℤ)) : ℂ → ℂ :=
  fun w => ((Matrix.SpecialLinearGroup.mapGL ℝ γ • ofComplex w : ℍ) : ℂ)

private lemma cfad_mob_coe (γ : SL(2, ℤ)) (v : ℍ) : cfad_mob γ ↑v = ↑(γ • v) := by
  simp only [cfad_mob, ofComplex_apply, MulAction.compHom_smul_def]

private lemma cfad_mob_analyticAt (γ : SL(2, ℤ)) (v : ℍ) : AnalyticAt ℂ (cfad_mob γ) ↑v :=
  analyticAt_smul (cfad_det_pos γ) v

private lemma cfad_mob_deriv_ne (γ : SL(2, ℤ)) (v : ℍ) : deriv (cfad_mob γ) ↑v ≠ 0 :=
  deriv_smul_ne_zero (cfad_det_pos γ) v

private lemma cfad_omega_rel {Γ : Subgroup SL(2, ℤ)} (f : CuspForm Γ 2) (F : ℍ → ℂ)
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) (t : ℂ) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (v : ℍ) :
    f (ofComplex (cfad_mob γ ↑v)) / (F (ofComplex (cfad_mob γ ↑v)) - t) * deriv (cfad_mob γ) ↑v
      = f (ofComplex ↑v) / (F (ofComplex ↑v) - t) := by
  have hderiv : deriv (cfad_mob γ) ↑v =
      (Matrix.SpecialLinearGroup.mapGL ℝ γ).val.det / denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) v ^ 2 := by
    first
      | simpa [cfad_mob] using deriv_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ γ) (cfad_det_pos γ) v
      | exact deriv_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ γ) (cfad_det_pos γ) v
  have hf : f (γ • v) * denom γ v ^ (-(2 : ℤ)) = f v := by
    have h1 := SlashInvariantForm.slash_action_eqn
      (F := CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ) 2) f
      (Matrix.SpecialLinearGroup.mapGL ℝ γ) (Subgroup.mem_map_of_mem _ hγ)
    calc f (γ • v) * denom γ v ^ (-(2 : ℤ)) = (⇑f ∣[(2 : ℤ)] γ) v := (SL_slash_apply _ _ _).symm
      _ = f v := by rw [SL_slash]; exact congrFun h1 v
  rw [cfad_mob_coe, ofComplex_apply, ofComplex_apply, hderiv, hΓ γ hγ v]
  have hfγ : f (γ • v) = f v * denom γ v ^ (2 : ℤ) := by
    rw [← hf]
    have hdγ : denom γ v ≠ 0 := denom_ne_zero _ v
    rw [mul_assoc, ← zpow_add₀ hdγ]
    norm_num
  rw [hfγ, cfad_det_one]
  have hdeq : denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑v = denom γ v := rfl
  rw [hdeq]
  have hdγ : denom γ v ≠ 0 := denom_ne_zero _ v
  field_simp
  norm_num

private lemma cfad_slashinv {Γ : Subgroup SL(2, ℤ)} (f : CuspForm Γ 2) (F : ℍ → ℂ)
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) (t : ℂ) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) :
    (fun v : ℍ => f v / (F v - t)) ∣[(2 : ℤ)] γ = fun v : ℍ => f v / (F v - t) := by
  funext v
  rw [SL_slash_apply]
  have hf : f (γ • v) * denom γ v ^ (-(2 : ℤ)) = f v := by
    have h1 := SlashInvariantForm.slash_action_eqn
      (F := CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ) 2) f
      (Matrix.SpecialLinearGroup.mapGL ℝ γ) (Subgroup.mem_map_of_mem _ hγ)
    calc f (γ • v) * denom γ v ^ (-(2 : ℤ)) = (⇑f ∣[(2 : ℤ)] γ) v := (SL_slash_apply _ _ _).symm
      _ = f v := by rw [SL_slash]; exact congrFun h1 v
  rw [hΓ γ hγ v, div_mul_eq_mul_div, ← hf]

private lemma cfad_decay {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (f : CuspForm Γ 2) (F : ℍ → ℂ)
    (t : ℂ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) (σ : SL(2, ℤ)) :
    ∃ δ : ℝ, 0 < δ ∧
      ((fun v : ℍ => f v / (F v - t)) ∣[(2 : ℤ)] σ) =O[atImInfty]
        fun τ : ℍ => Real.exp (-δ * τ.im) := by
  obtain ⟨L, hLt, hL⟩ := hcusp σ
  haveI : Finite (SL(2, ℤ) ⧸ Γ) := Subgroup.finite_quotient_of_finiteIndex
  obtain ⟨i, j, hij, hqe⟩ := Finite.exists_ne_map_eq_of_infinite
    (f := fun n : ℕ => QuotientGroup.mk (s := Γ) ((σ * ModularGroup.T * σ⁻¹) ^ n))
  wlog hlt : i < j generalizing i j
  · exact this j i hij.symm hqe.symm (by omega)
  set g : SL(2, ℤ) := σ * ModularGroup.T * σ⁻¹ with hg
  have hmem : g ^ (j - i) ∈ Γ := by
    have h1 : (g ^ i)⁻¹ * g ^ j ∈ Γ := QuotientGroup.eq.mp hqe
    have hcomm : (g ^ i)⁻¹ * g ^ j = g ^ j * (g ^ i)⁻¹ :=
      (((Commute.refl g).pow_pow i j).inv_left).eq
    rwa [hcomm, ← pow_sub g hlt.le] at h1
  set m : ℕ := j - i with hm
  have hm0 : 0 < m := by omega
  have hconj : g ^ m = σ * ModularGroup.T ^ m * σ⁻¹ := by
    rw [hg, conj_pow]
  have hper_pt : ∀ τ : ℍ, (⇑f ∣[(2 : ℤ)] σ) (((m : ℝ)) +ᵥ τ) = (⇑f ∣[(2 : ℤ)] σ) τ := by
    intro τ
    have hTm' : (ModularGroup.T ^ m) • τ = ((m : ℝ)) +ᵥ τ := by
      apply UpperHalfPlane.ext
      rw [← zpow_natCast ModularGroup.T m, ModularGroup.coe_T_zpow_smul_eq]
      push_cast [UpperHalfPlane.coe_vadd]
      ring
    have hslash : (⇑f ∣[(2 : ℤ)] σ) ∣[(2 : ℤ)] (ModularGroup.T ^ m) = ⇑f ∣[(2 : ℤ)] σ := by
      rw [← SlashAction.slash_mul]
      have hmul : σ * ModularGroup.T ^ m = g ^ m * σ := by
        rw [hconj]; group
      rw [hmul, SlashAction.slash_mul, SL_slash (γ := g ^ m),
        show (⇑f ∣[(2 : ℤ)] ((g ^ m : SL(2, ℤ)) : GL (Fin 2) ℝ)) = ⇑f from
          SlashInvariantForm.slash_action_eqn
            (F := CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) Γ) 2) f
            _ (Subgroup.mem_map_of_mem _ hmem)]
    have hev := congrFun hslash τ
    rw [SL_slash_apply] at hev
    have hden1 : denom (ModularGroup.T ^ m : SL(2, ℤ)) τ = 1 := by
      have h2 : ((ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ)) ^ m
          = ((ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) ^ m).map (Int.cast : ℤ → ℝ) := by
        simpa [RingHom.mapMatrix_apply] using
          (map_pow ((Int.castRingHom ℝ).mapMatrix) (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) m).symm
      have h4 : (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) ^ m = !![1, (m : ℤ); 0, 1] := by
        have h3 : (ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) ^ m
            = ((ModularGroup.T ^ m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          simp
        rw [h3, ← zpow_natCast ModularGroup.T m]
        exact_mod_cast ModularGroup.coe_T_zpow (m : ℤ)
      have hP : ((ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ)) ^ m
          = !![(1 : ℝ), (m : ℝ); 0, 1] := by
        rw [h2, h4]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      have hP' := hP
      try simp only [ModularGroup.coe_T] at hP'
      simp [denom, hP, hP']
    rw [hden1] at hev
    rw [hTm'] at hev
    simpa using hev
  have hper : Function.Periodic ((⇑f ∣[(2 : ℤ)] σ) ∘ ofComplex) (m : ℝ) := by
    intro z
    by_cases hz : 0 < z.im
    · have hz' : 0 < (z + (m : ℝ)).im := by simp [hz]
      have h1 : ofComplex (z + (m : ℝ)) = ((m : ℝ)) +ᵥ ofComplex z := by
        rw [ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz']
        exact UpperHalfPlane.ext (by push_cast [UpperHalfPlane.coe_vadd]; ring)
      simp only [Function.comp_apply, h1, hper_pt]
    · have h1 : (z + (m : ℝ)).im ≤ 0 := by
        simpa using not_lt.mp hz
      simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos (not_lt.mp hz),
        ofComplex_apply_of_im_nonpos h1]
  have hz0 : IsZeroAtImInfty (⇑f ∣[(2 : ℤ)] σ) :=
    CuspFormClass.zero_at_infty_slash (f := f) (g := σ)
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f ∣[(2 : ℤ)] σ) := by
    have h2 : ⇑(CuspForm.translate f ((σ : GL (Fin 2) ℝ))) = ⇑f ∣[(2 : ℤ)] σ :=
      CuspForm.coe_translate f σ
    have h1 : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ⇑(CuspForm.translate f ((σ : GL (Fin 2) ℝ))) :=
      (CuspForm.translate f ((σ : GL (Fin 2) ℝ))).holo'
    rwa [h2] at h1
  have hbdd : IsBoundedAtImInfty (⇑f ∣[(2 : ℤ)] σ) := hz0.boundedAtFilter
  have hdec := hz0.exp_decay_atImInfty (by positivity : (0 : ℝ) < m) hper hhol hbdd
  have hLne : L - t ≠ 0 := sub_ne_zero.mpr hLt
  have hinv : Filter.Tendsto (fun τ : ℍ => (F (σ • τ) - t)⁻¹) atImInfty (𝓝 (L - t)⁻¹) :=
    (hL.sub tendsto_const_nhds).inv₀ hLne
  have hden : (fun τ : ℍ => (F (σ • τ) - t)⁻¹) =O[atImInfty] (fun _ : ℍ => (1 : ℝ)) :=
    hinv.isBigO_one ℝ
  refine ⟨2 * Real.pi / m, by positivity, ?_⟩
  have heq : ((fun v : ℍ => f v / (F v - t)) ∣[(2 : ℤ)] σ)
      = fun τ : ℍ => (⇑f ∣[(2 : ℤ)] σ) τ * (F (σ • τ) - t)⁻¹ := by
    funext τ
    rw [SL_slash_apply, SL_slash_apply]
    field_simp
  rw [heq]
  exact (hdec.mul hden).congr (fun τ => rfl)
    (fun τ => by rw [mul_one]; congr 1; field_simp)

private lemma cfad_fhat_analytic {Γ : Subgroup SL(2, ℤ)} (f : CuspForm Γ 2) (τ : ℍ) :
    AnalyticAt ℂ (fun z => f (ofComplex z)) (τ : ℂ) := by
  have h1 : DifferentiableOn ℂ (⇑f ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    mdifferentiable_iff.mp f.holo'
  have h2 := h1.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  simpa [Function.comp_def] using h2

theorem solution (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (f : CuspForm Γ 2) (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • τ) = F τ) (t : ℂ)
    (hsimple : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ) ≤ 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ t ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ c : ℍ → ℂ,
      (∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ),
          f (ofComplex z) / (F (ofComplex z) - t) = c τ / (z - τ) + g z) ∧
      (∀ γ ∈ Γ, ∀ τ : ℍ, c (γ • τ) = c τ) ∧
      (∀ τ : ℍ, c τ ≠ 0 →
        0 < meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ)) ∧
      ∀ S : Finset ℍ, (∀ τ : ℍ, c τ ≠ 0 → ∃ σ ∈ S, ∃ γ ∈ Γ, γ • σ = τ) →
        (∀ σ ∈ S, ∀ σ' ∈ S, ∀ γ ∈ Γ, γ • σ = σ' → σ = σ') →
        ∑ σ ∈ S, c σ / Nat.card (MulAction.stabilizer Γ σ) = 0 := by
  have hFt : ∀ τ : ℍ, MeromorphicAt (fun z => F (ofComplex z) - t) (τ : ℂ) :=
    fun τ => (hF τ).sub (MeromorphicAt.const _ _)
  have hex : ∀ τ : ℍ, ∃ p : ℂ × (ℂ → ℂ), AnalyticAt ℂ p.2 (τ : ℂ) ∧
      (p.1 ≠ 0 → 0 < meromorphicOrderAt (fun z => F (ofComplex z) - t) (τ : ℂ)) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ),
        f (ofComplex z) / (F (ofComplex z) - t) = p.1 / (z - τ) + p.2 z :=
    fun τ => cfad_exists_expansion (cfad_fhat_analytic f τ) (hFt τ) (hsimple τ)
  choose p hpg hps hpe using hex
  refine ⟨fun τ => (p τ).1, fun τ => ⟨(p τ).2, hpg τ, hpe τ⟩, ?_, hps, ?_⟩
  ·
    intro γ hγ τ
    have hMb : cfad_mob γ⁻¹ ↑(γ • τ) = ↑τ := by
      rw [cfad_mob_coe, inv_smul_smul]
    obtain ⟨g2, hg2, hev2⟩ := cfad_resTransport (hpg τ) (hpe τ)
      (cfad_mob_analyticAt γ⁻¹ (γ • τ)) hMb (cfad_mob_deriv_ne γ⁻¹ (γ • τ))

    have hrel : ∀ᶠ w in 𝓝[≠] (↑(γ • τ) : ℂ),
        f (ofComplex w) / (F (ofComplex w) - t) = (p τ).1 / (w - ↑(γ • τ)) + g2 w := by
      have hopen : ∀ᶠ w in 𝓝 (↑(γ • τ) : ℂ), 0 < w.im :=
        (Complex.continuous_im.tendsto _).eventually (lt_mem_nhds (γ • τ).im_pos)
      filter_upwards [hev2, hopen.filter_mono nhdsWithin_le_nhds] with w hw hwim
      rw [← hw]
      have : ofComplex w = ⟨w, hwim⟩ := ofComplex_apply_of_im_pos hwim
      calc f (ofComplex w) / (F (ofComplex w) - t)
          = f (ofComplex (cfad_mob γ⁻¹ ↑(⟨w, hwim⟩ : ℍ))) /
              (F (ofComplex (cfad_mob γ⁻¹ ↑(⟨w, hwim⟩ : ℍ))) - t) *
              deriv (cfad_mob γ⁻¹) ↑(⟨w, hwim⟩ : ℍ) := by
            rw [cfad_omega_rel f F hΓ t (inv_mem hγ) ⟨w, hwim⟩, this]
        _ = f (ofComplex (cfad_mob γ⁻¹ w)) / (F (ofComplex (cfad_mob γ⁻¹ w)) - t) *
              deriv (cfad_mob γ⁻¹) w := by rw [show ((⟨w, hwim⟩ : ℍ) : ℂ) = w from rfl]
    show (p (γ • τ)).1 = (p τ).1
    exact cfad_resUnique (hpg (γ • τ)) hg2 (hpe (γ • τ)) hrel
  ·
    intro S hS hinj
    exact UpperHalfPlane.sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant Γ
      (fun v : ℍ => f v / (F v - t)) (fun τ => (p τ).1) S
      (fun γ hγ => cfad_slashinv f F hΓ t hγ)
      (fun σ => cfad_decay f F t hcusp σ)
      (fun τ => ⟨(p τ).2, hpg τ, hpe τ⟩) hS hinj

end S_UpperHalfPlane_exists_residue_cuspForm_div_sub
end P2MW
export P2MW.S_UpperHalfPlane_exists_residue_cuspForm_div_sub (solution)
