-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P43.tenderOperator
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T19:57:07.440414+00:00
-- url     : https://prove2.me/submissions/47026178-b7ed-4599-884c-684ddc3232f0

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

open Filter Topology

namespace X6G41

variable {κ : Type*} [Fintype κ]

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

variable {J : Type*} [Fintype J]

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

open scoped Matrix ComplexConjugate BigOperators

namespace X6F15

open QAlgorithms

variable {J : Type*} [Fintype J] [DecidableEq J]

lemma trace_cfc {X : Matrix J J ℂ} (hX : X.IsHermitian) (f : ℝ → ℝ) :
    (cfc f X).trace = ∑ i, ((f (hX.eigenvalues i) : ℝ) : ℂ) := by
  have hU := Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  rw [X6G41.cfc_spec hX, Matrix.trace_mul_cycle, hU, Matrix.one_mul, Matrix.trace_diagonal]

lemma sq_eq_cfc {X : Matrix J J ℂ} (hX : X.IsHermitian) :
    X * X = cfc (fun x : ℝ => x ^ 2) X := by
  have hU := Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  rw [X6G41.cfc_spec hX]
  conv_lhs => rw [X6G41.spec hX]
  set U := (hX.eigenvectorUnitary : Matrix J J ℂ)
  calc U * Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * star U *
        (U * Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * star U)
      = U * (Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * (star U * U) *
        Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ))) * star U := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hU, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
        congr 2; funext i; push_cast; ring

lemma traceNorm_herm {X : Matrix J J ℂ} (hX : X.IsHermitian) :
    traceNorm X = ∑ i, |hX.eigenvalues i| := by
  rw [traceNorm, hX.eq, sq_eq_cfc hX, ← cfc_comp Real.sqrt (fun x : ℝ => x ^ 2) X]
  have : (Real.sqrt ∘ fun x : ℝ => x ^ 2) = fun x => |x| := by
    funext x; simp [Real.sqrt_sq_eq_abs]
  rw [this, trace_cfc hX, Complex.re_sum]
  simp

lemma sum_sq_eig {X : Matrix J J ℂ} (hX : X.IsHermitian) :
    ∑ i, hX.eigenvalues i ^ 2 = (X * X).trace.re := by
  rw [sq_eq_cfc hX, trace_cfc hX, Complex.re_sum]
  exact Finset.sum_congr rfl (fun i _ => rfl)

/-- rank at most two ⇒ `(Σ|λ|)² ≤ 2 Σ λ²`. -/
lemma card_nonzero_le {X : Matrix J J ℂ} (hX : X.IsHermitian) (h : X.rank ≤ 2) :
    (∑ i, |hX.eigenvalues i|) ^ 2 ≤ 2 * ∑ i, hX.eigenvalues i ^ 2 := by
  set S := Finset.univ.filter (fun i => hX.eigenvalues i ≠ 0)
  have hS : S.card ≤ 2 := by
    have h1 : Fintype.card {i // hX.eigenvalues i ≠ 0} ≤ 2 := by
      rw [← hX.rank_eq_card_non_zero_eigs]; exact h
    simp only [S]
    rw [← Fintype.card_subtype]
    convert h1
  have e1 : ∑ i, |hX.eigenvalues i| = ∑ i ∈ S, |hX.eigenvalues i| := by
    rw [Finset.sum_filter_of_ne]; intro i _ h; simpa using h
  have e2 : ∑ i, hX.eigenvalues i ^ 2 = ∑ i ∈ S, |hX.eigenvalues i| ^ 2 := by
    rw [Finset.sum_filter_of_ne]
    · simp
    · intro i _ h; simpa using h
  rw [e1, e2]
  calc (∑ i ∈ S, |hX.eigenvalues i|) ^ 2 ≤ S.card * ∑ i ∈ S, |hX.eigenvalues i| ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ 2 * ∑ i ∈ S, |hX.eigenvalues i| ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun i _ => sq_nonneg _))
        exact_mod_cast hS

lemma rank_pd_sub (u v : EuclideanSpace ℂ J) :
    (pureDensity u - pureDensity v).rank ≤ 2 := by
  have e : pureDensity u - pureDensity v =
      (Matrix.of fun (i : J) (k : Fin 2) => (![u i, -v i] : Fin 2 → ℂ) k) *
        (Matrix.of fun (k : Fin 2) (j : J) => (![conj (u j), conj (v j)] : Fin 2 → ℂ) k) := by
    ext i j
    simp [pureDensity, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]
  rw [e]
  refine le_trans (Matrix.rank_mul_le_left _ _) ?_
  have := Matrix.rank_le_card_width (Matrix.of fun (i : J) (k : Fin 2) => (![u i, -v i] : Fin 2 → ℂ) k)
  simpa using this

lemma pd_herm (u : EuclideanSpace ℂ J) : (pureDensity u).IsHermitian := by
  ext i j
  simp [pureDensity, mul_comm]

lemma trace_pd_mul (u v : EuclideanSpace ℂ J) :
    (pureDensity u * pureDensity v).trace =
      (∑ a, u a * conj (v a)) * (∑ b, v b * conj (u b)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

/-- Pure-state trace distance bound. -/
lemma tn_pure (u v : EuclideanSpace ℂ J) (hu : ∑ a, u a * conj (u a) = 1)
    (hv : ∑ a, v a * conj (v a) = 1) (B : ℝ) (hB : ∑ a, u a * conj (v a) = (B : ℂ)) :
    traceNorm (pureDensity u - pureDensity v) ≤ 2 * Real.sqrt (1 - B ^ 2) := by
  have hX : (pureDensity u - pureDensity v).IsHermitian := (pd_herm u).sub (pd_herm v)
  rw [traceNorm_herm hX]
  have hsq := card_nonzero_le hX (rank_pd_sub u v)
  rw [sum_sq_eig hX] at hsq
  have hB' : ∑ b, v b * conj (u b) = (B : ℂ) := by
    have := congrArg (starRingEnd ℂ) hB
    rw [map_sum, Complex.conj_ofReal] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp [mul_comm]
  have htr : ((pureDensity u - pureDensity v) * (pureDensity u - pureDensity v)).trace.re =
      2 - 2 * B ^ 2 := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_sub, trace_pd_mul, trace_pd_mul, trace_pd_mul, trace_pd_mul, hu, hv, hB, hB']
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_re, Complex.one_im]
    ring
  rw [htr] at hsq
  have h0 : 0 ≤ ∑ i, |hX.eigenvalues i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  calc ∑ i, |hX.eigenvalues i| = Real.sqrt ((∑ i, |hX.eigenvalues i|) ^ 2) :=
        (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt (2 * (2 - 2 * B ^ 2)) := Real.sqrt_le_sqrt hsq
    _ = 2 * Real.sqrt (1 - B ^ 2) := by
        rw [show 2 * (2 - 2 * B ^ 2) = 2 ^ 2 * (1 - B ^ 2) by ring, Real.sqrt_mul (by norm_num),
          Real.sqrt_sq (by norm_num)]

/-- unit rows of a unitary. -/
lemma unit_rows (W : Matrix J J ℂ) (hW : W * star W = 1) (i : J) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have h2 := congrFun (congrFun hW i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h2
  simp only [Matrix.star_apply, X6G41.mul_star_eq] at h2
  have h3 := congrArg Complex.re h2
  rw [Complex.re_sum] at h3
  simpa using h3

/-- `Σ |r_i| ≤ ‖U diag(r) U*‖₁`. -/
lemma tn_lower (U : Matrix J J ℂ) (hU1 : star U * U = 1) (hU2 : U * star U = 1) (r : J → ℝ) :
    ∑ i, |r i| ≤ traceNorm (U * Matrix.diagonal (fun i => (r i : ℂ)) * star U) := by
  set Y := U * Matrix.diagonal (fun i => (r i : ℂ)) * star U
  have hY : Y.IsHermitian := by
    have hD : (Matrix.diagonal (fun i => (r i : ℂ)))ᴴ = Matrix.diagonal (fun i => (r i : ℂ)) := by
      rw [Matrix.diagonal_conjTranspose]; congr 1; funext i; simp
    unfold Y
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hD,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  rw [traceNorm_herm hY]
  set s : J → ℝ := fun i => if 0 ≤ r i then 1 else -1
  have hs : ∀ i, r i * s i = |r i| := by
    intro i; simp only [s]; split_ifs with h
    · rw [mul_one, abs_of_nonneg h]
    · rw [mul_neg_one, abs_of_neg (not_le.mp h)]
  have hsabs : ∀ i, |s i| = 1 := by intro i; simp only [s]; split_ifs <;> simp
  -- Σ|r| = Re tr(Y · U diag(s) U*)
  have e1 : (Y * (U * Matrix.diagonal (fun i => (s i : ℂ)) * star U)).trace.re = ∑ i, |r i| := by
    have : Y * (U * Matrix.diagonal (fun i => (s i : ℂ)) * star U) =
        U * (Matrix.diagonal (fun i => (r i : ℂ)) * (star U * U) *
          Matrix.diagonal (fun i => (s i : ℂ))) * star U := by
      simp only [Y, Matrix.mul_assoc]
    rw [this, hU1, Matrix.mul_one, Matrix.diagonal_mul_diagonal, Matrix.trace_mul_cycle, hU1,
      Matrix.one_mul, Matrix.trace_diagonal, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Complex.ofReal_mul, Complex.ofReal_re, hs]
  rw [← e1]
  have hV := Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2
  set V := (hY.eigenvectorUnitary : Matrix J J ℂ)
  have hYV : Y = V * Matrix.diagonal (fun i => ((hY.eigenvalues i : ℝ) : ℂ)) * star V :=
    X6G41.spec hY
  have key : (Y * (U * Matrix.diagonal (fun i => (s i : ℂ)) * star U)).trace =
      (V * Matrix.diagonal (fun i => ((hY.eigenvalues i : ℝ) : ℂ)) * star V *
        (U * Matrix.diagonal (fun i => (s i : ℂ)) * star U)).trace := by
    rw [← hYV]
  rw [key, X6G41.trace4, Complex.re_sum]
  have hW : (star V * U) * star (star V * U) = 1 := by
    rw [star_mul, star_star, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU2, Matrix.one_mul,
      Unitary.star_mul_self_of_mem hY.eigenvectorUnitary.2]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [Complex.re_sum, ← mul_one (|hY.eigenvalues i|), ← unit_rows _ hW i, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [X6G41.mul_star_eq, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h1 : hY.eigenvalues i * s j ≤ |hY.eigenvalues i| := by
    calc hY.eigenvalues i * s j ≤ |hY.eigenvalues i * s j| := le_abs_self _
      _ = |hY.eigenvalues i| := by rw [abs_mul, hsabs, mul_one]
  exact mul_le_mul_of_nonneg_right h1 (Complex.normSq_nonneg _)

end X6F15


noncomputable section

open scoped Matrix ComplexConjugate BigOperators

namespace X6R43

open QAlgorithms

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- rank ≤ 2 and trace zero ⇒ `(Σ|λ|)² = 2 Σ λ²`. -/
lemma card_two_eq {X : Matrix J J ℂ} (hX : X.IsHermitian) (h : X.rank ≤ 2) (htr : X.trace = 0) :
    (∑ i, |hX.eigenvalues i|) ^ 2 = 2 * ∑ i, hX.eigenvalues i ^ 2 := by
  set S := Finset.univ.filter (fun i => hX.eigenvalues i ≠ 0)
  have hS : S.card ≤ 2 := by
    have h1 : Fintype.card {i // hX.eigenvalues i ≠ 0} ≤ 2 := by
      rw [← hX.rank_eq_card_non_zero_eigs]; exact h
    simp only [S]
    rw [← Fintype.card_subtype]
    convert h1
  have e0 : ∑ i, hX.eigenvalues i = ∑ i ∈ S, hX.eigenvalues i := by
    rw [Finset.sum_filter_of_ne]; intro i _ h; exact h
  have e1 : ∑ i, |hX.eigenvalues i| = ∑ i ∈ S, |hX.eigenvalues i| := by
    rw [Finset.sum_filter_of_ne]; intro i _ h; simpa using h
  have e2 : ∑ i, hX.eigenvalues i ^ 2 = ∑ i ∈ S, hX.eigenvalues i ^ 2 := by
    rw [Finset.sum_filter_of_ne]; intro i _ h; simpa using h
  have hsum : ∑ i ∈ S, hX.eigenvalues i = 0 := by
    rw [← e0]
    have := congrArg Complex.re hX.trace_eq_sum_eigenvalues
    rw [htr, Complex.re_sum] at this
    simpa using this.symm
  rw [e1, e2]
  have hmem : ∀ i ∈ S, hX.eigenvalues i ≠ 0 := fun i hi => (Finset.mem_filter.mp hi).2
  interval_cases hc : S.card
  · rw [Finset.card_eq_zero.mp hc]; simp
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    rw [hi] at hsum hmem
    simp at hsum hmem
    exact absurd hsum hmem
  · obtain ⟨i, j, hij, hi⟩ := Finset.card_eq_two.mp hc
    rw [hi] at hsum ⊢
    rw [Finset.sum_pair hij] at hsum ⊢
    rw [Finset.sum_pair hij]
    have : hX.eigenvalues j = -hX.eigenvalues i := by linarith
    rw [this, abs_neg]
    nlinarith [sq_abs (hX.eigenvalues i)]

lemma tn_pure_eq (u v : EuclideanSpace ℂ J) (hu : ∑ a, u a * conj (u a) = 1)
    (hv : ∑ a, v a * conj (v a) = 1) :
    traceNorm (pureDensity u - pureDensity v) ^ 2 =
      4 * (1 - ((pureDensity u * pureDensity v).trace).re) := by
  have hX : (pureDensity u - pureDensity v).IsHermitian := (X6F15.pd_herm u).sub (X6F15.pd_herm v)
  have htr0 : (pureDensity u - pureDensity v).trace = 0 := by
    rw [Matrix.trace_sub]
    have e : ∀ w : EuclideanSpace ℂ J, (pureDensity w).trace = ∑ a, w a * conj (w a) := by
      intro w; simp [Matrix.trace, pureDensity]
    rw [e, e, hu, hv, sub_self]
  rw [X6F15.traceNorm_herm hX, card_two_eq hX (X6F15.rank_pd_sub u v) htr0, X6F15.sum_sq_eig hX]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_sub, X6F15.trace_pd_mul, X6F15.trace_pd_mul, X6F15.trace_pd_mul,
    X6F15.trace_pd_mul, hu, hv]
  have hc : ∑ b, v b * conj (u b) = conj (∑ a, u a * conj (v a)) := by
    rw [map_sum]; refine Finset.sum_congr rfl (fun a _ => ?_); simp [mul_comm]
  rw [hc]
  set z := ∑ a, u a * conj (v a)
  have hz : (conj z * z).re = Complex.normSq z := by
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]
  simp only [Complex.sub_re, one_mul, mul_one, Complex.one_re]
  rw [mul_comm z (conj z), hz]
  ring

lemma unit_sum (v : EuclideanSpace ℂ J) (hv : ‖v‖ = 1) : ∑ a, v a * conj (v a) = 1 := by
  have h := EuclideanSpace.norm_sq_eq v
  rw [hv, one_pow] at h
  have : ∑ a, v a * conj (v a) = ((∑ a, ‖v a‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [this, ← h]; simp

end X6R43


noncomputable section

open scoped Matrix ComplexConjugate BigOperators ComplexOrder

namespace X6M43

open QAlgorithms

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- `Re tr(X · U diag(s) U*) ≤ ‖X‖₁` for Hermitian `X`, unitary `U`, `|s| ≤ 1`. -/
lemma tr_le {X : Matrix J J ℂ} (hX : X.IsHermitian) (U : Matrix J J ℂ) (hU2 : U * star U = 1)
    (s : J → ℝ) (hs : ∀ j, |s j| ≤ 1) :
    (X * (U * Matrix.diagonal (fun i => (s i : ℂ)) * star U)).trace.re ≤ traceNorm X := by
  rw [X6F15.traceNorm_herm hX]
  have hV := Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2
  set V := (hX.eigenvectorUnitary : Matrix J J ℂ)
  have key : (X * (U * Matrix.diagonal (fun i => (s i : ℂ)) * star U)).trace =
      (V * Matrix.diagonal (fun i => ((hX.eigenvalues i : ℝ) : ℂ)) * star V *
        (U * Matrix.diagonal (fun i => (s i : ℂ)) * star U)).trace := by
    rw [← X6G41.spec hX]
  rw [key, X6G41.trace4, Complex.re_sum]
  have hW : (star V * U) * star (star V * U) = 1 := by
    rw [star_mul, star_star, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU2, Matrix.one_mul,
      Unitary.star_mul_self_of_mem hX.eigenvectorUnitary.2]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [Complex.re_sum, ← mul_one (|hX.eigenvalues i|), ← X6F15.unit_rows _ hW i, Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [X6G41.mul_star_eq, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h1 : hX.eigenvalues i * s j ≤ |hX.eigenvalues i| := by
    calc hX.eigenvalues i * s j ≤ |hX.eigenvalues i * s j| := le_abs_self _
      _ = |hX.eigenvalues i| * |s j| := abs_mul _ _
      _ ≤ |hX.eigenvalues i| * 1 := mul_le_mul_of_nonneg_left (hs j) (abs_nonneg _)
      _ = _ := mul_one _
  exact mul_le_mul_of_nonneg_right h1 (Complex.normSq_nonneg _)

/-- the sign matrix attains the trace norm. -/
lemma sign_attains {Z : Matrix J J ℂ} (hZ : Z.IsHermitian) :
    ∃ U : Matrix J J ℂ, U * star U = 1 ∧ ∃ s : J → ℝ, (∀ j, |s j| ≤ 1) ∧
      (Z * (U * Matrix.diagonal (fun i => (s i : ℂ)) * star U)).trace.re = traceNorm Z := by
  have hV := Unitary.star_mul_self_of_mem hZ.eigenvectorUnitary.2
  have hV2 := Unitary.mul_star_self_of_mem hZ.eigenvectorUnitary.2
  set V := (hZ.eigenvectorUnitary : Matrix J J ℂ)
  set s : J → ℝ := fun i => if 0 ≤ hZ.eigenvalues i then 1 else -1
  refine ⟨V, hV2, s, fun j => by simp only [s]; split_ifs <;> simp, ?_⟩
  rw [X6F15.traceNorm_herm hZ]
  have key : (Z * (V * Matrix.diagonal (fun i => (s i : ℂ)) * star V)).trace =
      (V * Matrix.diagonal (fun i => ((hZ.eigenvalues i : ℝ) : ℂ)) * star V *
        (V * Matrix.diagonal (fun i => (s i : ℂ)) * star V)).trace := by
    rw [← X6G41.spec hZ]
  rw [key]
  have e : V * Matrix.diagonal (fun i => ((hZ.eigenvalues i : ℝ) : ℂ)) * star V *
        (V * Matrix.diagonal (fun i => (s i : ℂ)) * star V) =
      V * (Matrix.diagonal (fun i => ((hZ.eigenvalues i : ℝ) : ℂ)) * (star V * V) *
        Matrix.diagonal (fun i => (s i : ℂ))) * star V := by
    simp only [Matrix.mul_assoc]
  rw [e, hV, Matrix.mul_one, Matrix.diagonal_mul_diagonal, Matrix.trace_mul_cycle, hV,
    Matrix.one_mul, Matrix.trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [s]; split_ifs with h
  · rw [mul_one, abs_of_nonneg h]
  · rw [mul_neg_one, abs_of_neg (not_le.mp h)]

/-- weighted triangle inequality for Hermitian matrices. -/
lemma tn_sum_le {ι : Type*} (t : Finset ι) (b : ι → ℝ) (hb : ∀ k, 0 ≤ b k)
    (X : ι → Matrix J J ℂ) (hX : ∀ k, (X k).IsHermitian) :
    traceNorm (∑ k ∈ t, (b k : ℂ) • X k) ≤ ∑ k ∈ t, b k * traceNorm (X k) := by
  have hZ : (∑ k ∈ t, (b k : ℂ) • X k).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.conjTranspose_smul, (hX k).eq, Complex.star_def, Complex.conj_ofReal]
  obtain ⟨U, hU, s, hs, heq⟩ := sign_attains hZ
  rw [← heq, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_le_sum (fun k _ => ?_)
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  exact mul_le_mul_of_nonneg_left (tr_le (hX k) U hU s hs) (hb k)

lemma density_decomp {ρ : Matrix J J ℂ} (hρ : ρ.IsHermitian) :
    ρ = ∑ i, ((hρ.eigenvalues i : ℝ) : ℂ) • pureDensity (hρ.eigenvectorBasis i) := by
  conv_lhs => rw [X6G41.spec hρ]
  ext k l
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, Matrix.sum_apply,
    Matrix.smul_apply, pureDensity, Matrix.of_apply, smul_eq_mul,
    Matrix.IsHermitian.eigenvectorUnitary_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [RCLike.star_def]; ring

lemma pd_psd (u : EuclideanSpace ℂ J) : (pureDensity u).PosSemidef := by
  have e : pureDensity u = (Matrix.of fun (_ : Unit) (j : J) => conj (u j))ᴴ *
      (Matrix.of fun (_ : Unit) (j : J) => conj (u j)) := by
    refine Matrix.ext fun i j => ?_
    simp [pureDensity, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [e]; exact Matrix.posSemidef_conjTranspose_mul_self _

lemma eig_le_one {P : Matrix J J ℂ} (hP : P.PosSemidef) (htr : P.trace = 1) (i : J) :
    hP.1.eigenvalues i ≤ 1 := by
  have h0 := hP.eigenvalues_nonneg
  have key : (P.trace).re = 1 := by rw [htr]; simp
  rw [hP.1.trace_eq_sum_eigenvalues, Complex.re_sum] at key
  have hs : ∑ k, hP.1.eigenvalues k = 1 := by simpa using key
  rw [← hs]
  exact Finset.single_le_sum (f := fun k => hP.1.eigenvalues k) (fun j _ => h0 j)
    (Finset.mem_univ i)

/-- part (a): `tr(P X) ≤ ‖X‖₁/2` for a density `P` and traceless Hermitian `X`. -/
lemma part_a {P X : Matrix J J ℂ} (hP : P.PosSemidef) (htrP : P.trace = 1) (hX : X.IsHermitian)
    (htr : X.trace = 0) : (X * P).trace.re ≤ traceNorm X / 2 := by
  have hU2 := Unitary.mul_star_self_of_mem hP.1.eigenvectorUnitary.2
  set U := (hP.1.eigenvectorUnitary : Matrix J J ℂ)
  set s : J → ℝ := fun i => 2 * hP.1.eigenvalues i - 1
  have hs : ∀ j, |s j| ≤ 1 := by
    intro j; simp only [s]
    rw [abs_le]; constructor <;> nlinarith [hP.eigenvalues_nonneg j, eig_le_one hP htrP j]
  have h := tr_le hX U hU2 s hs
  have e : U * Matrix.diagonal (fun i => (s i : ℂ)) * star U = (2 : ℂ) • P - 1 := by
    have hPs : P = U * Matrix.diagonal (fun i => ((hP.1.eigenvalues i : ℝ) : ℂ)) * star U :=
      X6G41.spec hP.1
    have h1 : (1 : Matrix J J ℂ) = U * Matrix.diagonal (fun _ => (1 : ℂ)) * star U := by
      rw [Matrix.diagonal_one, Matrix.mul_one, hU2]
    conv_rhs => rw [hPs, h1]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.sub_mul, ← Matrix.mul_sub,
      ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    congr 3; funext i; simp only [s, Pi.smul_apply, smul_eq_mul]; push_cast; ring
  rw [e, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
    htr, sub_zero, smul_eq_mul] at h
  have h2 : (2 * (X * P).trace).re = 2 * (X * P).trace.re := by simp [Complex.mul_re]
  rw [h2] at h
  linarith

end X6M43


noncomputable section

open scoped Matrix ComplexConjugate BigOperators ComplexOrder

namespace X6T43

open QAlgorithms

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- eigenvalues of an effect lie in `[0,1]`. -/
lemma eff_eig {X : Matrix J J ℂ} (hX : IsEffect X) (i : J) :
    0 ≤ hX.1.1.eigenvalues i ∧ hX.1.1.eigenvalues i ≤ 1 := by
  refine ⟨hX.1.eigenvalues_nonneg i, ?_⟩
  set e := (hX.1.1.eigenvectorBasis i : J → ℂ)
  have h1 := hX.2.dotProduct_mulVec_nonneg e
  have he : X *ᵥ e = (hX.1.1.eigenvalues i : ℂ) • e := by
    have := hX.1.1.mulVec_eigenvectorBasis i
    rw [this]; ext k; simp [RCLike.real_smul_eq_coe_smul (K := ℂ), e]
  have hn : star e ⬝ᵥ e = 1 := by
    have := (hX.1.1.eigenvectorBasis).orthonormal.1 i
    have h2 := X6R43.unit_sum (hX.1.1.eigenvectorBasis i) this
    rw [← h2]; simp only [dotProduct, Pi.star_apply, RCLike.star_def, e]
    exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, he, dotProduct_sub, dotProduct_smul, hn] at h1
  simp only [smul_eq_mul, mul_one] at h1
  have := (Complex.nonneg_iff.mp h1).1
  simp at this
  linarith

lemma conj_diag_psd (U : Matrix J J ℂ) (d : J → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (U * Matrix.diagonal (fun i => (d i : ℂ)) * star U).PosSemidef := by
  have hD : (Matrix.diagonal (fun i => (d i : ℂ))).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]; intro i; exact_mod_cast hd i
  have := hD.mul_mul_conjTranspose_same U
  rwa [Matrix.star_eq_conjTranspose]

def qf (A : Matrix J J ℂ) (ψ : J → ℂ) : ℂ := star ψ ⬝ᵥ (A *ᵥ ψ)

section eff

variable {X : Matrix J J ℂ} (hX : IsEffect X)

include hX in
lemma S_spec : cfc Real.sqrt X = (hX.1.1.eigenvectorUnitary : Matrix J J ℂ) *
    Matrix.diagonal (fun i => ((Real.sqrt (hX.1.1.eigenvalues i) : ℝ) : ℂ)) *
    star (hX.1.1.eigenvectorUnitary : Matrix J J ℂ) := X6G41.cfc_spec hX.1.1 _

include hX in
lemma S_herm : (cfc Real.sqrt X).IsHermitian := by
  rw [S_spec hX, Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.diagonal_conjTranspose, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  congr 2; congr 1; funext i; simp

include hX in
lemma SS : cfc Real.sqrt X * cfc Real.sqrt X = X := by
  have hU := Unitary.star_mul_self_of_mem hX.1.1.eigenvectorUnitary.2
  rw [S_spec hX]
  conv_rhs => rw [X6G41.spec hX.1.1]
  set U := (hX.1.1.eigenvectorUnitary : Matrix J J ℂ)
  calc U * Matrix.diagonal (fun i => ((Real.sqrt (hX.1.1.eigenvalues i) : ℝ) : ℂ)) * star U *
        (U * Matrix.diagonal (fun i => ((Real.sqrt (hX.1.1.eigenvalues i) : ℝ) : ℂ)) * star U)
      = U * (Matrix.diagonal (fun i => ((Real.sqrt (hX.1.1.eigenvalues i) : ℝ) : ℂ)) * (star U * U) *
        Matrix.diagonal (fun i => ((Real.sqrt (hX.1.1.eigenvalues i) : ℝ) : ℂ))) * star U := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hU, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
        congr 2; congr 1; funext i
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (eff_eig hX i).1]

include hX in
lemma S_sub_psd : (cfc Real.sqrt X - X).PosSemidef := by
  have e : cfc Real.sqrt X - X = (hX.1.1.eigenvectorUnitary : Matrix J J ℂ) *
      Matrix.diagonal (fun i => ((Real.sqrt (hX.1.1.eigenvalues i) - hX.1.1.eigenvalues i : ℝ) : ℂ)) *
      star (hX.1.1.eigenvectorUnitary : Matrix J J ℂ) := by
    rw [S_spec hX]
    have hXs := X6G41.spec hX.1.1
    calc _ = (hX.1.1.eigenvectorUnitary : Matrix J J ℂ) *
          Matrix.diagonal (fun i => ((Real.sqrt (hX.1.1.eigenvalues i) : ℝ) : ℂ)) *
          star (hX.1.1.eigenvectorUnitary : Matrix J J ℂ) -
          (hX.1.1.eigenvectorUnitary : Matrix J J ℂ) *
          Matrix.diagonal (fun i => ((hX.1.1.eigenvalues i : ℝ) : ℂ)) *
          star (hX.1.1.eigenvectorUnitary : Matrix J J ℂ) := by congr 1
      _ = _ := ?_
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
    congr 3; funext i; push_cast; ring
  rw [e]
  apply conj_diag_psd
  intro i
  obtain ⟨h0, h1⟩ := eff_eig hX i
  have : hX.1.1.eigenvalues i ≤ Real.sqrt (hX.1.1.eigenvalues i) := by
    calc hX.1.1.eigenvalues i = Real.sqrt (hX.1.1.eigenvalues i) * Real.sqrt (hX.1.1.eigenvalues i) :=
          (Real.mul_self_sqrt h0).symm
      _ ≤ Real.sqrt (hX.1.1.eigenvalues i) * 1 :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr h1) (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  linarith

end eff

lemma qf_re_nonneg {A : Matrix J J ℂ} (hA : A.PosSemidef) (ψ : J → ℂ) : 0 ≤ (qf A ψ).re :=
  (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg ψ)).1

lemma qf_im {A : Matrix J J ℂ} (hA : A.IsHermitian) (ψ : J → ℂ) : (qf A ψ).im = 0 := by
  have := hA.im_star_dotProduct_mulVec_self ψ
  simpa [qf] using this

lemma pd_conj (S : Matrix J J ℂ) (hS : S.IsHermitian) (ψ : EuclideanSpace ℂ J) :
    S * pureDensity ψ * S = pureDensity (WithLp.toLp 2 (S *ᵥ ψ.ofLp)) := by
  ext i j
  simp only [Matrix.mul_apply, pureDensity, Matrix.of_apply, Matrix.mulVec, dotProduct,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [← hS.apply a j]
  simp [Complex.star_def]; ring

lemma tr_pd (A : Matrix J J ℂ) (ψ : EuclideanSpace ℂ J) :
    (pureDensity ψ * A).trace = qf A ψ.ofLp := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, pureDensity, Matrix.of_apply, qf,
    dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring

lemma qf_one (ψ : EuclideanSpace ℂ J) (hψ : ∑ a, ψ a * conj (ψ a) = 1) :
    (qf 1 ψ.ofLp).re = 1 := by
  have : qf 1 ψ.ofLp = ∑ a, ψ a * conj (ψ a) := by
    simp only [qf, Matrix.one_mulVec, dotProduct, Pi.star_apply, RCLike.star_def]
    exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  rw [this, hψ]; simp

lemma one_state {X : Matrix J J ℂ} (hX : IsEffect X) (ψ : EuclideanSpace ℂ J)
    (hψ : ∑ a, ψ a * conj (ψ a) = 1) :
    traceNorm (pureDensity ψ - cfc Real.sqrt X * pureDensity ψ * cfc Real.sqrt X) ≤
      2 * Real.sqrt (1 - (qf X ψ.ofLp).re) := by
  set S := cfc Real.sqrt X
  have hS := S_herm hX
  rw [pd_conj S hS ψ]
  set φ : EuclideanSpace ℂ J := WithLp.toLp 2 (S *ᵥ ψ.ofLp)
  have hA : (pureDensity ψ - pureDensity φ).IsHermitian := (X6F15.pd_herm ψ).sub (X6F15.pd_herm φ)
  have hcs := X6F15.card_nonzero_le hA (X6F15.rank_pd_sub ψ φ)
  rw [X6F15.sum_sq_eig hA] at hcs
  have hb : ∑ a, φ a * conj (φ a) = qf X ψ.ofLp := by
    have e : ∑ a, φ a * conj (φ a) = star (S *ᵥ ψ.ofLp) ⬝ᵥ (S *ᵥ ψ.ofLp) := by
      simp only [dotProduct, Pi.star_apply, RCLike.star_def, φ]
      exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    rw [e, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      ← Matrix.dotProduct_mulVec, hS.eq, SS hX]
    rfl
  have hz : ∑ a, ψ a * conj (φ a) = qf S ψ.ofLp := by
    have e : ∑ a, ψ a * conj (φ a) = star (S *ᵥ ψ.ofLp) ⬝ᵥ ψ.ofLp := by
      simp only [dotProduct, Pi.star_apply, RCLike.star_def, φ]
      exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    rw [e, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hS.eq]
    rfl
  have hz' : ∑ b, φ b * conj (ψ b) = conj (qf S ψ.ofLp) := by
    rw [← hz, map_sum]; refine Finset.sum_congr rfl (fun a _ => ?_); simp [mul_comm]
  set q := (qf X ψ.ofLp).re
  set r := (qf S ψ.ofLp).re
  have hq0 : 0 ≤ q := qf_re_nonneg hX.1 _
  have hrq : q ≤ r := by
    have := qf_re_nonneg (S_sub_psd hX) ψ.ofLp
    simp only [qf, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at this
    simp only [q, r, qf]; linarith
  have hq1 : q ≤ 1 := by
    have := qf_re_nonneg hX.2 ψ.ofLp
    have h1 : (qf 1 ψ.ofLp).re = 1 := qf_one ψ hψ
    simp only [qf, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at this
    simp only [qf] at h1; simp only [q, qf]; linarith
  have hXq : qf X ψ.ofLp = (q : ℂ) := by
    apply Complex.ext <;> simp [q, qf_im hX.1.1]
  have htr : ((pureDensity ψ - pureDensity φ) * (pureDensity ψ - pureDensity φ)).trace.re =
      1 + q ^ 2 - 2 * Complex.normSq (qf S ψ.ofLp) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_sub, X6F15.trace_pd_mul, X6F15.trace_pd_mul, X6F15.trace_pd_mul,
      X6F15.trace_pd_mul, hψ, hb, hz, hz', hXq]
    have e1 : (qf S ψ.ofLp * conj (qf S ψ.ofLp)).re = Complex.normSq (qf S ψ.ofLp) := by
      rw [Complex.mul_conj, Complex.ofReal_re]
    have e2 : (conj (qf S ψ.ofLp) * qf S ψ.ofLp).re = Complex.normSq (qf S ψ.ofLp) := by
      rw [mul_comm, e1]
    simp only [Complex.sub_re, Complex.add_re, one_mul, Complex.one_re] at *
    rw [e1, e2]
    simp [Complex.mul_re, sq]; ring
  have hns : r ^ 2 ≤ Complex.normSq (qf S ψ.ofLp) := by
    rw [Complex.normSq_apply]; nlinarith [sq_nonneg (qf S ψ.ofLp).im]
  rw [htr] at hcs
  rw [X6F15.traceNorm_herm hA]
  have h0 : 0 ≤ ∑ i, |hA.eigenvalues i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hle : (∑ i, |hA.eigenvalues i|) ^ 2 ≤ (2 * Real.sqrt (1 - q)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    nlinarith
  exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).mp hle

end X6T43

open QAlgorithms QAlgorithms.Papers.Independent.Renew46.P43

attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {I : Type*} [Fintype I] [DecidableEq I]
    (rho X : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hX : IsEffect X)
    (lambda : ℝ) (herror : 1 - effectProb rho X ≤ lambda) (hlambda : lambda ≤ 1) :
    traceNorm (rho - cfc Real.sqrt X * rho * cfc Real.sqrt X) ≤ Real.sqrt (8 * lambda) := by
  have hdec := X6M43.density_decomp hrho.1.1
  set p := hrho.1.1.eigenvalues
  set e := hrho.1.1.eigenvectorBasis
  set S := cfc Real.sqrt X
  have hS := X6T43.S_herm hX
  have hp0 : ∀ k, 0 ≤ p k := hrho.1.eigenvalues_nonneg
  have hp1 : ∑ k, p k = 1 := by
    have key : (rho.trace).re = 1 := by rw [hrho.2]; simp
    rw [hrho.1.1.trace_eq_sum_eigenvalues, Complex.re_sum] at key
    simpa using key
  have he1 : ∀ k, ∑ a, e k a * conj (e k a) = 1 := fun k => X6R43.unit_sum (e k) (e.orthonormal.1 k)
  set q : I → ℝ := fun k => (X6T43.qf X (e k).ofLp).re
  have hdiff : rho - S * rho * S = ∑ k, (p k : ℂ) • (pureDensity (e k) - S * pureDensity (e k) * S) := by
    conv_lhs => rw [hdec]
    rw [Finset.mul_sum, Finset.sum_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, Finset.sum_sub_distrib]
  have hherm : ∀ k, (pureDensity (e k) - S * pureDensity (e k) * S).IsHermitian := by
    intro k; rw [X6T43.pd_conj S hS]; exact (X6F15.pd_herm _).sub (X6F15.pd_herm _)
  have hT : traceNorm (rho - S * rho * S) ≤ ∑ k, p k * (2 * Real.sqrt (1 - q k)) := by
    rw [hdiff]
    calc _ ≤ ∑ k, p k * traceNorm (pureDensity (e k) - S * pureDensity (e k) * S) :=
          X6M43.tn_sum_le _ p hp0 _ hherm
      _ ≤ _ := Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left (X6T43.one_state hX (e k) (he1 k)) (hp0 k))
  have hq1 : ∀ k, q k ≤ 1 := by
    intro k
    have := X6T43.qf_re_nonneg hX.2 (e k).ofLp
    have h1 : (X6T43.qf 1 (e k).ofLp).re = 1 := X6T43.qf_one (e k) (he1 k)
    simp only [X6T43.qf, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re] at this
    simp only [X6T43.qf] at h1; simp only [q, X6T43.qf]; linarith
  have hF : effectProb rho X = ∑ k, p k * q k := by
    rw [effectProb]
    conv_lhs => rw [hdec]
    rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, X6T43.tr_pd]
  have hJ : (∑ k, p k * Real.sqrt (1 - q k)) ^ 2 ≤ ∑ k, p k * (1 - q k) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => Real.sqrt (p k))
      (fun k => Real.sqrt (p k) * Real.sqrt (1 - q k))
    have e1 : ∀ k, Real.sqrt (p k) * (Real.sqrt (p k) * Real.sqrt (1 - q k)) =
        p k * Real.sqrt (1 - q k) := by
      intro k; rw [← mul_assoc, Real.mul_self_sqrt (hp0 k)]
    have e2 : ∀ k, Real.sqrt (p k) ^ 2 = p k := fun k => Real.sq_sqrt (hp0 k)
    have e3 : ∀ k, (Real.sqrt (p k) * Real.sqrt (1 - q k)) ^ 2 = p k * (1 - q k) := by
      intro k; rw [mul_pow, Real.sq_sqrt (hp0 k), Real.sq_sqrt (by linarith [hq1 k])]
    simp only [e1, e2, e3, hp1, one_mul] at this
    exact this
  have hsum : ∑ k, p k * (1 - q k) = 1 - ∑ k, p k * q k := by
    rw [Finset.sum_congr rfl (fun k _ => mul_sub (p k) 1 (q k)), Finset.sum_sub_distrib]
    simp only [mul_one]; rw [hp1]
  have hY : 0 ≤ ∑ k, p k * Real.sqrt (1 - q k) :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hp0 k) (Real.sqrt_nonneg _))
  have hY2 : ∑ k, p k * Real.sqrt (1 - q k) ≤ Real.sqrt lambda := by
    rw [← Real.sqrt_sq hY]
    apply Real.sqrt_le_sqrt
    rw [hF] at herror
    linarith
  have h2 : ∑ k, p k * (2 * Real.sqrt (1 - q k)) = 2 * ∑ k, p k * Real.sqrt (1 - q k) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
  have hl0 : 0 ≤ lambda := by
    have : effectProb rho X ≤ 1 := by
      rw [hF]
      calc ∑ k, p k * q k ≤ ∑ k, p k * 1 :=
            Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hq1 k) (hp0 k))
        _ = 1 := by simp [hp1]
    linarith
  have h8 : 2 * Real.sqrt lambda ≤ Real.sqrt (8 * lambda) := by
    rw [show (8 : ℝ) * lambda = 2 ^ 2 * (2 * lambda) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
    have : Real.sqrt lambda ≤ Real.sqrt (2 * lambda) := Real.sqrt_le_sqrt (by linarith)
    linarith
  linarith

