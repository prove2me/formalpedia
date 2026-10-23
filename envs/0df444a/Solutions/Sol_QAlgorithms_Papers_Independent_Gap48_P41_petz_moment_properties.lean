-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P41.petz_moment_properties
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T18:59:31.476265+00:00
-- url     : https://prove2.me/submissions/6e4ee35d-db03-45a8-8a13-2ea7fb351ea7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P41

noncomputable section

open Filter Topology

namespace X6G41

variable {κ : Type} [Fintype κ]

/-- `F(s) = Σ w_k exp(s ℓ_k)`. -/
def lse (w l : κ → ℝ) (s : ℝ) : ℝ := ∑ k, w k * Real.exp (s * l k)

lemma lse_hasDerivAt (w l : κ → ℝ) (s : ℝ) :
    HasDerivAt (lse w l) (lse (fun k => w k * l k) l s) s := by
  unfold lse
  have : HasDerivAt (fun s => ∑ k, w k * Real.exp (s * l k))
      (∑ k, w k * (Real.exp (s * l k) * l k)) s := by
    apply HasDerivAt.fun_sum
    intro k _
    apply HasDerivAt.const_mul
    have := ((hasDerivAt_id s).mul_const (l k)).exp
    simpa using this
  convert this using 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

lemma lse_pos (w l : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (h0 : 0 < lse w l 0) (s : ℝ) :
    0 < lse w l s := by
  unfold lse at *
  simp only [zero_mul, Real.exp_zero, mul_one] at h0
  obtain ⟨k, -, hk⟩ := Finset.exists_lt_of_sum_lt (by simpa using h0 :
    ∑ k : κ, (0 : ℝ) < ∑ k, w k)
  calc 0 < w k * Real.exp (s * l k) := mul_pos hk (Real.exp_pos _)
    _ ≤ _ := Finset.single_le_sum (f := fun k => w k * Real.exp (s * l k))
        (fun j _ => mul_nonneg (hw j) (Real.exp_pos _).le) (Finset.mem_univ k)

lemma psi_hasDerivAt (w l : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (h0 : 0 < lse w l 0) (s : ℝ) :
    HasDerivAt (fun s => Real.log (lse w l s))
      (lse (fun k => w k * l k) l s / lse w l s) s :=
  (lse_hasDerivAt w l s).log (lse_pos w l hw h0 s).ne'

lemma deriv_psi (w l : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (h0 : 0 < lse w l 0) :
    deriv (fun s => Real.log (lse w l s)) =
      fun s => lse (fun k => w k * l k) l s / lse w l s :=
  funext fun s => (psi_hasDerivAt w l hw h0 s).deriv

lemma cs (w l : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (s : ℝ) :
    lse (fun k => w k * l k) l s ^ 2 ≤
      lse w l s * lse (fun k => w k * l k * l k) l s := by
  unfold lse
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k => Real.sqrt (w k * Real.exp (s * l k)))
    (fun k => l k * Real.sqrt (w k * Real.exp (s * l k)))
  have e : ∀ k, Real.sqrt (w k * Real.exp (s * l k)) ^ 2 = w k * Real.exp (s * l k) := fun k =>
    Real.sq_sqrt (mul_nonneg (hw k) (Real.exp_pos _).le)
  have e1 : ∑ k, Real.sqrt (w k * Real.exp (s * l k)) * (l k * Real.sqrt (w k * Real.exp (s * l k)))
      = ∑ k, w k * l k * Real.exp (s * l k) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [mul_comm (l k), ← mul_assoc, ← sq, e]; ring
  have e2 : ∑ k, Real.sqrt (w k * Real.exp (s * l k)) ^ 2 = ∑ k, w k * Real.exp (s * l k) :=
    Finset.sum_congr rfl (fun k _ => e k)
  have e3 : ∑ k, (l k * Real.sqrt (w k * Real.exp (s * l k))) ^ 2
      = ∑ k, w k * l k * l k * Real.exp (s * l k) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [mul_pow, e]; ring
  rw [e1, e2, e3] at this
  exact this

lemma psi_convex (w l : κ → ℝ) (hw : ∀ k, 0 ≤ w k) (h0 : 0 < lse w l 0) :
    ConvexOn ℝ Set.univ (fun s => Real.log (lse w l s)) := by
  have hd := deriv_psi w l hw h0
  have hd2 : ∀ s, HasDerivAt (fun s => lse (fun k => w k * l k) l s / lse w l s)
      ((lse (fun k => w k * l k * l k) l s * lse w l s -
        lse (fun k => w k * l k) l s * lse (fun k => w k * l k) l s) / lse w l s ^ 2) s :=
    fun s => (lse_hasDerivAt _ l s).div (lse_hasDerivAt w l s) (lse_pos w l hw h0 s).ne'
  apply convexOn_univ_of_deriv2_nonneg
  · exact fun s => (psi_hasDerivAt w l hw h0 s).differentiableAt
  · rw [hd]; exact fun s => (hd2 s).differentiableAt
  · intro s
    rw [Function.iterate_succ_apply, Function.iterate_one, hd, (hd2 s).deriv]
    apply div_nonneg _ (sq_nonneg _)
    have := cs w l hw s
    nlinarith

/-- If `g` has positive derivative at `x`, then `g` exceeds `g x` just to the right and is
below it just to the left. -/
lemma right_gt {g : ℝ → ℝ} {d x : ℝ} (hg : HasDerivAt g d x) (hd : 0 < d) :
    ∀ᶠ t in 𝓝[>] x, g x < g t := by
  have h1 := hasDerivAt_iff_tendsto_slope.mp hg
  have h2 : Tendsto (slope g x) (𝓝[>] x) (𝓝 d) := h1.mono_left (nhdsWithin_mono _ (by
    intro t ht; exact ne_of_gt ht))
  filter_upwards [h2.eventually (lt_mem_nhds hd), self_mem_nhdsWithin] with t ht htx
  rw [slope_def_field] at ht
  have : 0 < t - x := sub_pos.mpr htx
  have := (div_pos_iff_of_pos_right this).mp ht
  linarith

lemma left_lt {g : ℝ → ℝ} {d x : ℝ} (hg : HasDerivAt g d x) (hd : 0 < d) :
    ∀ᶠ t in 𝓝[<] x, g t < g x := by
  have h1 := hasDerivAt_iff_tendsto_slope.mp hg
  have h2 : Tendsto (slope g x) (𝓝[<] x) (𝓝 d) := h1.mono_left (nhdsWithin_mono _ (by
    intro t ht; exact ne_of_lt ht))
  filter_upwards [h2.eventually (lt_mem_nhds hd), self_mem_nhdsWithin] with t ht htx
  rw [slope_def_field] at ht
  have : t - x < 0 := sub_neg.mpr htx
  have := (div_pos_iff.mp ht)
  rcases this with h | h
  · linarith [h.2]
  · linarith [h.1]

lemma exists_right_gt {g : ℝ → ℝ} {d x : ℝ} (hg : HasDerivAt g d x) (hd : 0 < d) (b : ℝ)
    (hb : x < b) : ∃ t ∈ Set.Ioo x b, g x < g t := by
  have := (right_gt hg hd).and (Ioo_mem_nhdsGT hb)
  obtain ⟨t, h1, h2⟩ := this.exists
  exact ⟨t, h2, h1⟩

lemma exists_left_lt {g : ℝ → ℝ} {d x : ℝ} (hg : HasDerivAt g d x) (hd : 0 < d) (a : ℝ)
    (ha : a < x) : ∃ t ∈ Set.Ioo a x, g t < g x := by
  have := (left_lt hg hd).and (Ioo_mem_nhdsLT ha)
  obtain ⟨t, h1, h2⟩ := this.exists
  exact ⟨t, h2, h1⟩

/-- Abstract version of the properties for a convex everywhere differentiable `ψ` with
`ψ 0 = 0`. -/
theorem abstract_props (ψ : ℝ → ℝ) (hc : ConvexOn ℝ Set.univ ψ)
    (hd : ∀ s, HasDerivAt ψ (deriv ψ s) s) (D : ℝ) (hD : deriv ψ 0 = D) (h0 : ψ 0 = 0) :
    (∀ lambda : ℝ, D < lambda →
      0 < sSup ((fun s : ℝ => lambda * s - ψ s) '' Set.Icc 0 1)) ∧
    (∀ lambda : ℝ, D ≤ lambda → lambda ≤ deriv ψ 1 → ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (IsGreatest ((fun t : ℝ => lambda * t - ψ t) '' Set.Icc 0 1)
        (lambda * s - ψ s) ↔ deriv ψ s = lambda)) := by
  have hcont : Continuous ψ := continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt
  have hh : ∀ lambda s, HasDerivAt (fun t => lambda * t - ψ t) (lambda - deriv ψ s) s := by
    intro lambda s
    have := ((hasDerivAt_id s).const_mul lambda).sub (hd s)
    simp only [id, mul_one] at this
    exact this
  constructor
  · intro lambda hl
    obtain ⟨t, ht, hgt⟩ := exists_right_gt (hh lambda 0) (by rw [hD]; linarith) 1 one_pos
    have hbdd : BddAbove ((fun s : ℝ => lambda * s - ψ s) '' Set.Icc 0 1) :=
      (isCompact_Icc.image (by fun_prop)).bddAbove
    have := le_csSup hbdd ⟨t, Set.Ioo_subset_Icc_self ht, rfl⟩
    simp only [mul_zero, h0, sub_zero] at hgt
    linarith
  · intro lambda hl1 hl2 s hs
    constructor
    · rintro ⟨-, hmax⟩
      have hle : ∀ t ∈ Set.Icc (0 : ℝ) 1, lambda * t - ψ t ≤ lambda * s - ψ s :=
        fun t ht => hmax ⟨t, ht, rfl⟩
      by_contra hne
      rcases lt_trichotomy (deriv ψ s) lambda with hlt | hgt
      · -- derivative of h positive: s < 1 needed
        have hs1 : s < 1 := by
          rcases eq_or_lt_of_le hs.2 with h | h
          · subst h; linarith
          · exact h
        obtain ⟨t, ht, hgt⟩ := exists_right_gt (hh lambda s) (by linarith) 1 hs1
        have := hle t ⟨by linarith [ht.1, hs.1], ht.2.le⟩
        linarith
      · rcases hgt with h | hgt
        · exact hne h
        have hs0 : 0 < s := by
          rcases eq_or_lt_of_le hs.1 with h | h
          · subst h; linarith
          · exact h
        have hneg : HasDerivAt (fun t => -(lambda * t - ψ t)) (-(lambda - deriv ψ s)) s :=
          (hh lambda s).neg
        obtain ⟨t, ht, hlt⟩ := exists_left_lt hneg (by linarith) 0 hs0
        have := hle t ⟨ht.1.le, by linarith [ht.2, hs.2]⟩
        linarith
    · intro hds
      refine ⟨⟨s, hs, rfl⟩, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      simp only
      rcases lt_trichotomy t s with h | h | h
      · have := hc.slope_le_of_hasDerivAt (Set.mem_univ t) (Set.mem_univ s) h (hd s)
        rw [slope_def_field, hds, div_le_iff₀ (by linarith)] at this
        linarith
      · rw [h]
      · have := hc.le_slope_of_hasDerivAt (Set.mem_univ s) (Set.mem_univ t) h (hd s)
        rw [slope_def_field, hds, le_div_iff₀ (by linarith)] at this
        linarith

end X6G41


noncomputable section

open scoped Matrix ComplexOrder BigOperators

namespace X6G41

variable {J : Type} [Fintype J]

lemma cfc_spec [DecidableEq J] {X : Matrix J J ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    cfc f X = (hX.eigenvectorUnitary : Matrix J J ℂ) *
      Matrix.diagonal (fun i => ((f (hX.eigenvalues i) : ℝ) : ℂ)) *
      star (hX.eigenvectorUnitary : Matrix J J ℂ) := by
  rw [hX.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rfl

lemma spec [DecidableEq J] {X : Matrix J J ℂ} (hX : X.IsHermitian) :
    X = (hX.eigenvectorUnitary : Matrix J J ℂ) *
      Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) *
      star (hX.eigenvectorUnitary : Matrix J J ℂ) := by
  have hs := hX.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  exact hs

lemma trace4 [DecidableEq J] (U V : Matrix J J ℂ) (d1 d2 : J → ℂ) :
    (U * Matrix.diagonal d1 * star U * (V * Matrix.diagonal d2 * star V)).trace =
      ∑ i, ∑ j, d1 i * d2 j * ((star U * V) i j * star ((star U * V) i j)) := by
  have e : U * Matrix.diagonal d1 * star U * (V * Matrix.diagonal d2 * star V) =
      U * (Matrix.diagonal d1 * (star U * V) * Matrix.diagonal d2 * star V) := by
    simp only [Matrix.mul_assoc]
  have e2 : Matrix.diagonal d1 * (star U * V) * Matrix.diagonal d2 * star V * U =
      Matrix.diagonal d1 * (star U * V) * Matrix.diagonal d2 * star (star U * V) := by
    simp only [star_mul, star_star, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, e2, Matrix.trace]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.star_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

lemma term_eq (a b c s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (if a = 0 then 0 else Real.rpow a (1 + s)) * (if b = 0 then 0 else Real.rpow b (-s)) * c =
      (if 0 < a ∧ 0 < b then c * a else 0) * Real.exp (s * (Real.log a - Real.log b)) := by
  by_cases h0 : a = 0
  · simp [h0]
  by_cases h1 : b = 0
  · simp [h1]
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm h1)
  simp only [h0, h1, if_false, ha', hb', and_self, if_true]
  rw [Real.rpow_eq_pow, Real.rpow_eq_pow, Real.rpow_def_of_pos ha', Real.rpow_def_of_pos hb']
  have e : c * a * Real.exp (s * (Real.log a - Real.log b)) =
      c * (Real.exp (Real.log a) * Real.exp (s * (Real.log a - Real.log b))) := by
    rw [Real.exp_log ha']; ring
  rw [e, ← Real.exp_add, ← Real.exp_add, mul_comm _ c]
  congr 2; ring

section spectral

variable [DecidableEq J] (ρ σ : Matrix J J ℂ) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)

/-- overlap matrix of the two eigenbases -/
def W : Matrix J J ℂ :=
  star (hρ.1.eigenvectorUnitary : Matrix J J ℂ) * (hσ.1.eigenvectorUnitary : Matrix J J ℂ)

def cc (i j : J) : ℝ := Complex.normSq (W ρ σ hρ hσ i j)

def ww (k : J × J) : ℝ :=
  if 0 < hρ.1.eigenvalues k.1 ∧ 0 < hσ.1.eigenvalues k.2 then
    cc ρ σ hρ hσ k.1 k.2 * hρ.1.eigenvalues k.1 else 0

def ll (k : J × J) : ℝ := Real.log (hρ.1.eigenvalues k.1) - Real.log (hσ.1.eigenvalues k.2)

lemma ww_nonneg (k : J × J) : 0 ≤ ww ρ σ hρ hσ k := by
  unfold ww; split_ifs with h
  · exact mul_nonneg (Complex.normSq_nonneg _) h.1.le
  · exact le_refl _

lemma mul_star_eq (z : ℂ) : z * star z = ((Complex.normSq z : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj]

lemma rowsum (i : J) : ∑ j, cc ρ σ hρ hσ i j = 1 := by
  have hU := Unitary.star_mul_self_of_mem hρ.1.eigenvectorUnitary.2
  have hV := Unitary.mul_star_self_of_mem hσ.1.eigenvectorUnitary.2
  have h1 : W ρ σ hρ hσ * star (W ρ σ hρ hσ) = 1 := by
    unfold W
    rw [star_mul, star_star, Matrix.mul_assoc, ← Matrix.mul_assoc _ (star _), hV,
      Matrix.one_mul, hU]
  have h2 := congrFun (congrFun h1 i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h2
  simp only [Matrix.star_apply] at h2
  have h3 := congrArg Complex.re h2
  rw [Complex.re_sum] at h3
  simp only [mul_star_eq, Complex.ofReal_re, Complex.one_re] at h3
  exact h3

lemma ortho (hsupp : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) (i j : J)
    (ha : 0 < hρ.1.eigenvalues i) (hb : hσ.1.eigenvalues j = 0) : W ρ σ hρ hσ i j = 0 := by
  set U := (hρ.1.eigenvectorUnitary : Matrix J J ℂ)
  set V := (hσ.1.eigenvectorUnitary : Matrix J J ℂ)
  have hU := Unitary.star_mul_self_of_mem hρ.1.eigenvectorUnitary.2
  have hV := Unitary.star_mul_self_of_mem hσ.1.eigenvectorUnitary.2
  have hsV : σ * V = V * Matrix.diagonal (fun i => ((hσ.1.eigenvalues i : ℝ) : ℂ)) := by
    conv_lhs => rw [spec hσ.1]
    rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  have hUr : star U * ρ = Matrix.diagonal (fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ)) * star U := by
    conv_lhs => rw [spec hρ.1]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hcol : σ *ᵥ (fun k => V k j) = 0 := by
    funext k
    have := congrFun (congrFun hsV k) j
    rw [Matrix.mul_diagonal, hb] at this
    simp only [Complex.ofReal_zero, mul_zero] at this
    rw [Pi.zero_apply, ← this, Matrix.mul_apply]
    rfl
  have hker : (fun k => V k j) ∈ LinearMap.ker ρ.mulVecLin :=
    hsupp (by rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]; exact hcol)
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hker
  have hρV : ∀ k, (ρ * V) k j = 0 := by
    intro k
    have := congrFun hker k
    rw [Matrix.mul_apply]; exact this
  have e : (star U * ρ * V) i j = 0 := by
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp [hρV]
  rw [hUr, Matrix.mul_assoc, Matrix.diagonal_mul] at e
  exact (mul_eq_zero.mp e).resolve_left (by exact_mod_cast ha.ne')

lemma F_eq (s : ℝ) :
    (cfc (fun x : ℝ => if x = 0 then 0 else Real.rpow x (1 + s)) ρ *
      cfc (fun x : ℝ => if x = 0 then 0 else Real.rpow x (-s)) σ).trace.re =
      lse (ww ρ σ hρ hσ) (ll ρ σ hρ hσ) s := by
  rw [cfc_spec hρ.1, cfc_spec hσ.1, trace4, Complex.re_sum, lse, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mul_star_eq, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  have := term_eq (hρ.1.eigenvalues i) (hσ.1.eigenvalues j) (cc ρ σ hρ hσ i j) s
    (hρ.eigenvalues_nonneg i) (hσ.eigenvalues_nonneg j)
  exact this

lemma pair_eq (hsupp : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) (i j : J) (x : ℝ) :
    ww ρ σ hρ hσ (i, j) * x = cc ρ σ hρ hσ i j * hρ.1.eigenvalues i * x := by
  unfold ww
  have ha := hρ.eigenvalues_nonneg i
  have hb := hσ.eigenvalues_nonneg j
  split_ifs with h
  · rfl
  · rcases eq_or_lt_of_le ha with ha0 | ha0
    · simp [← ha0]
    · have hb0 : hσ.1.eigenvalues j = 0 := by
        by_contra hne
        exact h ⟨ha0, lt_of_le_of_ne hb (Ne.symm hne)⟩
      simp [cc, ortho ρ σ hρ hσ hsupp i j ha0 hb0]

lemma F_zero (hsupp : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) (htr : ρ.trace = 1) :
    lse (ww ρ σ hρ hσ) (ll ρ σ hρ hσ) 0 = 1 := by
  have e1 : ∀ k, ww ρ σ hρ hσ k * Real.exp (0 * ll ρ σ hρ hσ k) =
      cc ρ σ hρ hσ k.1 k.2 * hρ.1.eigenvalues k.1 * 1 := by
    rintro ⟨i, j⟩
    rw [zero_mul, Real.exp_zero]
    exact pair_eq ρ σ hρ hσ hsupp i j 1
  rw [lse, Finset.sum_congr rfl (fun k _ => e1 k), Fintype.sum_prod_type]
  simp only [mul_one]
  have e2 : ∀ i, ∑ j, cc ρ σ hρ hσ i j * hρ.1.eigenvalues i = hρ.1.eigenvalues i := by
    intro i; rw [← Finset.sum_mul, rowsum, one_mul]
  rw [Finset.sum_congr rfl (fun i _ => e2 i)]
  have := congrArg Complex.re (hρ.1.trace_eq_sum_eigenvalues)
  rw [htr, Complex.re_sum] at this
  simp only [Complex.ofReal_re, Complex.one_re] at this
  exact this.symm

lemma D_eq (hsupp : LinearMap.ker σ.mulVecLin ≤ LinearMap.ker ρ.mulVecLin) :
    (ρ * (cfc Real.log ρ - cfc Real.log σ)).trace.re =
      lse (fun k => ww ρ σ hρ hσ k * ll ρ σ hρ hσ k) (ll ρ σ hρ hσ) 0 := by
  have hU := Unitary.star_mul_self_of_mem hρ.1.eigenvectorUnitary.2
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  rw [cfc_spec hρ.1, cfc_spec hσ.1]
  have key : ∀ Y : Matrix J J ℂ, (ρ * Y).trace = ((hρ.1.eigenvectorUnitary : Matrix J J ℂ) *
      Matrix.diagonal (fun i => ((hρ.1.eigenvalues i : ℝ) : ℂ)) *
      star (hρ.1.eigenvectorUnitary : Matrix J J ℂ) * Y).trace := fun Y => by
    rw [← spec hρ.1]
  rw [key, key, trace4, trace4, hU, Complex.re_sum, Complex.re_sum]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, star_one, star_zero,
    ite_mul, zero_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [lse, Fintype.sum_prod_type, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.re_sum]
  have e3 : (((hρ.1.eigenvalues i : ℝ) : ℂ) * ((Real.log (hρ.1.eigenvalues i) : ℝ) : ℂ)).re =
      ∑ j, cc ρ σ hρ hσ i j * (hρ.1.eigenvalues i * Real.log (hρ.1.eigenvalues i)) := by
    rw [← Finset.sum_mul, rowsum, one_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [e3, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [zero_mul, Real.exp_zero, mul_one, pair_eq ρ σ hρ hσ hsupp i j, mul_star_eq,
    ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re, ll]
  simp only [cc, W]
  ring

end spectral

end X6G41


noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P41
open scoped Matrix ComplexOrder BigOperators
open Filter QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)
open QAlgorithms.Papers.Independent.Dependency50.P28 (tr SupportLE relativeEntropy)
open QAlgorithms.Papers.Independent.Claimed50.P15 (legendre)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I : Type} [Fintype I] [DecidableEq I]

theorem solution [Nonempty I]
    (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) :
    ConvexOn ℝ (Set.Icc 0 1) (petzPsi rho sigma) ∧
    petzPsi rho sigma 0 = 0 ∧
    HasDerivAt (petzPsi rho sigma) (relativeEntropy rho sigma).toReal 0 ∧
    (∀ lambda : ℝ, (relativeEntropy rho sigma).toReal < lambda →
      0 < petzPhi rho sigma lambda) ∧
    (∀ lambda : ℝ, (relativeEntropy rho sigma).toReal ≤ lambda →
      lambda ≤ deriv (petzPsi rho sigma) 1 → ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (IsGreatest ((fun t : ℝ => lambda * t - petzPsi rho sigma t) '' Set.Icc 0 1)
        (lambda * s - petzPsi rho sigma s) ↔ deriv (petzPsi rho sigma) s = lambda)) := by
  have hρ := hrho.1
  have hσ := hsigma.1
  have hs : LinearMap.ker sigma.mulVecLin ≤ LinearMap.ker rho.mulVecLin := hsupp
  set w := X6G41.ww rho sigma hρ hσ
  set l := X6G41.ll rho sigma hρ hσ
  have hw : ∀ k, 0 ≤ w k := X6G41.ww_nonneg rho sigma hρ hσ
  have hF0 : X6G41.lse w l 0 = 1 := X6G41.F_zero rho sigma hρ hσ hs hrho.2
  have h0 : 0 < X6G41.lse w l 0 := by rw [hF0]; exact one_pos
  have hpsi : petzPsi rho sigma = fun s => Real.log (X6G41.lse w l s) := by
    funext s
    rw [petzPsi, tr, supportPower, supportPower]
    rw [X6G41.F_eq rho sigma hρ hσ s]
  have hD : (relativeEntropy rho sigma).toReal = X6G41.lse (fun k => w k * l k) l 0 := by
    rw [relativeEntropy, if_pos hsupp, EReal.toReal_coe, tr, tr, hrho.2, Complex.one_re, div_one]
    exact X6G41.D_eq rho sigma hρ hσ hs
  have hder : ∀ s, HasDerivAt (petzPsi rho sigma) (deriv (petzPsi rho sigma) s) s := by
    intro s
    rw [hpsi, X6G41.deriv_psi w l hw h0]
    exact X6G41.psi_hasDerivAt w l hw h0 s
  have hder0 : deriv (petzPsi rho sigma) 0 = (relativeEntropy rho sigma).toReal := by
    rw [hpsi, X6G41.deriv_psi w l hw h0, hD]
    show _ / X6G41.lse w l 0 = _
    rw [hF0, div_one]
  have hconv : ConvexOn ℝ Set.univ (petzPsi rho sigma) := by
    rw [hpsi]; exact X6G41.psi_convex w l hw h0
  have hz : petzPsi rho sigma 0 = 0 := by rw [hpsi]; simp only [hF0, Real.log_one]
  obtain ⟨A4, A5⟩ := X6G41.abstract_props (petzPsi rho sigma) hconv hder _ hder0 hz
  refine ⟨hconv.subset (Set.subset_univ _) (convex_Icc 0 1), hz, ?_, ?_, A5⟩
  · rw [← hder0]; exact hder 0
  · intro lambda hl
    exact A4 lambda hl
