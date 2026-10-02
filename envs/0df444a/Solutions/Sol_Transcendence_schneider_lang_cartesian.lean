-- Prove2me | solution 1 for Transcendence.schneider_lang_cartesian
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T09:02:47.227202+00:00
-- url     : https://prove2.me/submissions/d5794591-f446-470e-94ef-2abdb6abf967

import Mathlib
import Theorems.Thm_Transcendence_exp_monomials_liouville_lower
import Theorems.Thm_Transcendence_exists_exp_monomials_small_on_grid
import Theorems.Thm_Transcendence_grid_schwarz_cauchy
import Theorems.Thm_Transcendence_exists_schneider_lang_parameters
import Theorems.Thm_Transcendence_exp_monomials_ne_zero

/-!
# The criterion of Schneider–Lang for `ℂ^{d₀} × (ℂ^×)^{d₁}`, `d₀ ≤ 1` (DALAG Cor. 4.2, §4.6)

Waldschmidt's direct proof (§4.6), with the correction of `E12_BLUEPRINT.md` (flag 4): the auxiliary
function vanishes to **total** order `< n·E·T` at the grid points, which is what survives the change of
variables `z ↦ Σ z_j y_j` in the Schwarz step. Here `n = |ι|`, `d = d₀ + d₁ > n`, and
`F(z) = Σ p_{τ,t} z_{k₀}^τ e^{⟨t₁x₁ + ⋯ + t_{d₁}x_{d₁}, z⟩}` (`τ ≤ d₀T`, `tᵢ ≤ T`).

1. Choose `k₀` and `d₀ ≤ 1` from `ι₀`.
2. The constant `C` of Liouville's inequality (4.14) (`exp_monomials_liouville_lower`), the constant `c` of
   the grid Schwarz lemma (`grid_schwarz_cauchy`), and the parameters `S₁, T, E, U, N`
   (`exists_schneider_lang_parameters`).
3. The auxiliary function `F` (`exists_exp_monomials_small_on_grid`): small on the grid, (4.16).
4. (4.14) against (4.16) and (4.17): every derivative of order `< nET` vanishes on the grid.
5. Node 4 (`exp_monomials_ne_zero`) gives a first non-vanishing order `M' ≥ nET` at a grid point `s'`;
   put `u = ⌊M'/n⌋`, so `M' ≤ 2nu`.
6. Schwarz on the grid with `ρ = u/T`, against (4.14) at `s'`, contradicts (4.19).
-/

namespace SchneiderLangCartesian

lemma cmm_eq_zero_of_basis {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (μ : ContinuousMultilinearMap ℂ (fun _ : Fin k => ι → ℂ) ℂ)
    (h : ∀ L : Fin k → ι, μ (fun l => Pi.single (L l) 1) = 0) : μ = 0 := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℂ ι)
  intro L
  simpa [Pi.basisFun_apply] using h L

lemma analyticAt_linear {ι : Type*} [Fintype ι] (c : ι → ℂ) (z : ι → ℂ) :
    AnalyticAt ℂ (fun z : ι → ℂ => ∑ ν, c ν * z ν) z := by
  have : (fun z : ι → ℂ => ∑ ν, c ν * z ν) = ∑ ν, fun z : ι → ℂ => c ν * z ν := by
    funext z; simp
  rw [this]
  exact Finset.analyticAt_sum _ fun ν _ =>
    analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) ν).analyticAt z)

lemma analytic_expMono {ι : Type*} [Fintype ι] (k₀ : ι) (τ : ℕ) (c : ι → ℂ) :
    AnalyticOnNhd ℂ (fun z : ι → ℂ => z k₀ ^ τ * Complex.exp (∑ ν, c ν * z ν)) Set.univ := by
  intro z _
  have h1 : AnalyticAt ℂ (fun z : ι → ℂ => z k₀) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) k₀).analyticAt z
  exact (h1.pow τ).mul (analyticAt_linear c z).cexp

end SchneiderLangCartesian

open SchneiderLangCartesian in
/-- **The criterion of Schneider–Lang for `ℂ^{d₀} × (ℂ^×)^{d₁}`, `d₀ ≤ 1`** (Waldschmidt, DALAG,
Cor. 4.2, by the direct proof of §4.6 with total-order vanishing). -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {d₁ : ℕ}
    (x : Fin d₁ → ι → ℂ) (hxalg : ∀ i ν, IsAlgebraic ℚ (x i ν)) (hxind : LinearIndependent ℚ x)
    (y : ι → ι → ℂ) (hy : LinearIndependent ℂ y)
    (ι₀ : Option ι) (hdim : Fintype.card ι < ι₀.elim 0 (fun _ => 1) + d₁)
    (hy₀ : ∀ k, ι₀ = some k → ∀ j, IsAlgebraic ℚ (y j k))
    (hexp : ∀ i j, IsAlgebraic ℚ (Complex.exp (∑ ν, x i ν * y j ν))) : False := by
  classical
  /- Step 1: `k₀` and `d₀`. If `ι₀ = none`, then `ι` is not empty: otherwise `x` would be a non-empty
  family of zero vectors. -/
  obtain ⟨k₀, d₀, hd₀, hdim', hy₀'⟩ : ∃ (k₀ : ι) (d₀ : ℕ), d₀ ≤ 1 ∧ Fintype.card ι < d₀ + d₁ ∧
      (d₀ = 1 → ∀ j, IsAlgebraic ℚ (y j k₀)) := by
    cases ι₀ with
    | some k => exact ⟨k, 1, le_rfl, hdim, fun _ => hy₀ k rfl⟩
    | none =>
      have hd : Fintype.card ι < 0 + d₁ := hdim
      have hne : Nonempty ι := by
        by_contra h
        rw [not_nonempty_iff] at h
        exact hxind.ne_zero ⟨0, by omega⟩ (funext fun ν => (h.false ν).elim)
      obtain ⟨k⟩ := hne
      exact ⟨k, 0, Nat.zero_le _, hd, fun h => absurd h (by norm_num)⟩
  set n := Fintype.card ι with hn_def
  have hn : 1 ≤ n := Fintype.card_pos_iff.mpr ⟨k₀⟩
  /- Step 2: the constants of (4.14) and of the Schwarz step, and the parameters. -/
  obtain ⟨C, hC, hLiou⟩ := Transcendence.exp_monomials_liouville_lower x hxalg y hexp k₀ hd₀ hy₀'
  obtain ⟨c, hc, hGrid⟩ := Transcendence.grid_schwarz_cauchy (by omega) y hy
  set cx : ℝ := ∑ i, ∑ ν, ‖x i ν‖ with hcx_def
  have hcx : 0 ≤ cx := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun ν _ => norm_nonneg _
  set cy : ℝ := ∑ j, ‖y j‖ with hcy_def
  have hcy : 0 ≤ cy := Finset.sum_nonneg fun j _ => norm_nonneg _
  obtain ⟨S₁, T, E, U, N, hS₁, hT, hE, hU, hN, hSL, h417, h419⟩ :=
    Transcendence.exists_schneider_lang_parameters n (d₀ + d₁) C cx cy c hn hdim' hC hcx hcy hc
  /- Step 3: the auxiliary function, small on the grid (4.16). -/
  obtain ⟨p, hp0, hpN, hCau, hgrowth⟩ := Transcendence.exists_exp_monomials_small_on_grid x y k₀
    hd₀ le_rfl le_rfl hS₁ hT hU hN hSL
  set F : (ι → ℂ) → ℂ := fun z => ∑ l, (p l : ℂ) * (z k₀ ^ (l.1 : ℕ) *
    Complex.exp (∑ ν, (∑ i, ((l.2 i : ℕ) : ℂ) * x i ν) * z ν)) with hF_def
  have hFan : AnalyticOnNhd ℂ F Set.univ := by
    intro z _
    have : F = ∑ l, fun z => (p l : ℂ) * (z k₀ ^ (l.1 : ℕ) *
        Complex.exp (∑ ν, (∑ i, ((l.2 i : ℕ) : ℂ) * x i ν) * z ν)) := by
      funext z; simp [hF_def]
    rw [this]
    exact Finset.analyticAt_sum _ fun l _ =>
      analyticAt_const.mul (analytic_expMono k₀ _ _ z trivial)
  set q : (ι → Fin S₁) → (ι → ℂ) := fun s => ∑ j, ((s j : ℕ) : ℂ) • y j with hq_def
  have hLiou' : ∀ (s : ι → Fin S₁) (k : ℕ) (L : Fin k → ι),
      iteratedFDeriv ℂ k F (q s) (fun l => Pi.single (L l) 1) ≠ 0 →
      -(C * (N + k * (1 + Real.log T) + T * (S₁ + Real.log (1 + k)))) ≤
        Real.log ‖iteratedFDeriv ℂ k F (q s) (fun l => Pi.single (L l) 1)‖ :=
    fun s k L hne => hLiou T S₁ p N s k L hT hN.le hpN hne
  /- Step 4: vanishing to total order `< n E T` at every grid point. -/
  have hvan : ∀ k, k < n * (E * T) → ∀ s, iteratedFDeriv ℂ k F (q s) = 0 := by
    intro k hk s
    apply cmm_eq_zero_of_basis
    intro L
    by_contra hne
    have h1 := hLiou' s k L hne
    have h2 : ‖iteratedFDeriv ℂ k F (q s) (fun l => Pi.single (L l) 1)‖ ≤
        k.factorial * Real.exp (-U) := hCau s k L
    have h3 : Real.log ‖iteratedFDeriv ℂ k F (q s) (fun l => Pi.single (L l) 1)‖ ≤
        Real.log (k.factorial : ℝ) - U := by
      have := Real.log_le_log (norm_pos_iff.mpr hne) h2
      rw [Real.log_mul (by exact_mod_cast (Nat.factorial_pos k).ne') (Real.exp_pos _).ne',
        Real.log_exp] at this
      linarith
    have h4 := h417 k hk
    linarith
  /- Step 5: the first non-vanishing derivative (node 4). -/
  have hp' : (fun l => (p l : ℂ)) ≠ 0 := by
    intro h; apply hp0; funext l; have := congrFun h l; simpa using this
  obtain ⟨k₁, hk₁⟩ := Transcendence.exp_monomials_ne_zero x hxind k₀ (T₀ := d₀ * T) (T₁ := T)
    (fun l => (p l : ℂ)) hp'
  set s₀ : ι → Fin S₁ := fun _ => ⟨0, by omega⟩ with hs₀
  have hq0 : q s₀ = 0 := by simp [hq_def, hs₀]
  have hex : ∃ k, ∃ s, iteratedFDeriv ℂ k F (q s) ≠ 0 := ⟨k₁, s₀, by rw [hq0]; exact hk₁⟩
  obtain ⟨M', hM'_def⟩ : ∃ M', M' = Nat.find hex := ⟨_, rfl⟩
  obtain ⟨s', hs'⟩ : ∃ s, iteratedFDeriv ℂ M' F (q s) ≠ 0 := hM'_def ▸ Nat.find_spec hex
  have hmin : ∀ k < M', ∀ s, iteratedFDeriv ℂ k F (q s) = 0 := by
    intro k hk s
    by_contra h
    rw [hM'_def] at hk
    exact Nat.find_min hex hk ⟨s, h⟩
  have hM'ge : n * (E * T) ≤ M' := by
    by_contra h
    exact hs' (hvan M' (not_le.mp h) s')
  obtain ⟨L', hL'⟩ : ∃ L' : Fin M' → ι,
      iteratedFDeriv ℂ M' F (q s') (fun l => Pi.single (L' l) 1) ≠ 0 := by
    by_contra hall
    apply hs'
    apply cmm_eq_zero_of_basis
    intro L
    by_contra hL
    exact hall ⟨L, hL⟩
  /- `u = ⌊M'/n⌋ ≥ E T` and `M' ≤ 2 n u`. -/
  obtain ⟨u, hu_def⟩ : ∃ u, u = M' / n := ⟨_, rfl⟩
  have hu : E * T ≤ u := by
    rw [hu_def, Nat.le_div_iff_mul_le (by omega)]
    linarith [mul_comm n (E * T)]
  have hTu : T ≤ u := le_trans (Nat.le_mul_of_pos_left T (by omega)) hu
  have hnu : n * u ≤ M' := by rw [hu_def, mul_comm]; exact Nat.div_mul_le_self M' n
  have hMu : M' ≤ 2 * n * u := by
    have h1 : M' < n * (u + 1) := by rw [hu_def]; exact Nat.lt_mul_div_succ M' (by omega)
    have h2 : n ≤ n * u := Nat.le_mul_of_pos_right n (by omega)
    have h3 : n * (u + 1) = n * u + n := by ring
    have h4 : 2 * n * u = n * u + n * u := by ring
    omega
  /- Step 6: Schwarz on the grid with `ρ = u/T`, then (4.14) at `s'`, against (4.19). -/
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hupos : (0 : ℝ) < u := by exact_mod_cast (lt_of_lt_of_le hT hTu)
  set ρ : ℝ := (u : ℝ) / T with hρ_def
  have hρ1 : 1 ≤ ρ := by rw [hρ_def, le_div_iff₀ hTpos, one_mul]; exact_mod_cast hTu
  have hρpos : 0 < ρ := by linarith
  set RF : ℝ := c * S₁ * ρ with hRF_def
  have hRF1 : 1 ≤ RF := by
    have hS₁' : (1 : ℝ) ≤ S₁ := by exact_mod_cast hS₁
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ c * S₁ * ρ := by gcongr
  have hRFpos : 0 < RF := by linarith
  set B : ℝ := ((T : ℝ) + 1) ^ (d₀ + d₁) * Real.exp N * RF ^ T * Real.exp (cx * T * RF) with hB_def
  have hupper : ‖iteratedFDeriv ℂ M' F (q s') (fun l => Pi.single (L' l) 1)‖ ≤
      M'.factorial * (n * ρ⁻¹ ^ (u * S₁) * B) :=
    hGrid F hFan u S₁ M' ρ B hS₁ hρ1 hnu hmin (fun w hw => hgrowth RF hRF1 w hw) s' L'
  have hlow := hLiou' s' M' L' hL'
  have hlogup := Real.log_le_log (norm_pos_iff.mpr hL') hupper
  have hA : (0 : ℝ) < ((T : ℝ) + 1) ^ (d₀ + d₁) := by positivity
  have hA2 : (0 : ℝ) < ((T : ℝ) + 1) ^ (d₀ + d₁) * Real.exp N * RF ^ T := by positivity
  have hBpos : 0 < B := by positivity
  have hlogB : Real.log B = (d₀ + d₁ : ℕ) * Real.log (T + 1) + N + T * Real.log RF +
      cx * T * RF := by
    rw [hB_def, Real.log_mul hA2.ne' (Real.exp_pos _).ne', Real.log_mul (by positivity)
      (pow_pos hRFpos _).ne', Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_pow,
      Real.log_pow, Real.log_exp, Real.log_exp]
  have hfac : (0 : ℝ) < M'.factorial := by exact_mod_cast Nat.factorial_pos M'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hρu : (0 : ℝ) < ρ⁻¹ ^ (u * S₁) := pow_pos (inv_pos.mpr hρpos) _
  rw [Real.log_mul hfac.ne' (mul_pos (mul_pos hnpos hρu) hBpos).ne',
    Real.log_mul (mul_pos hnpos hρu).ne' hBpos.ne', Real.log_mul hnpos.ne' hρu.ne',
    Real.log_pow, Real.log_inv, hlogB] at hlogup
  have hfinal := h419 u M' hu hMu
  have e : c * S₁ * u / T = RF := by rw [hRF_def, hρ_def, mul_div_assoc]
  rw [e] at hfinal
  push_cast at hlogup hfinal
  linarith only [hlow, hlogup, hfinal]
