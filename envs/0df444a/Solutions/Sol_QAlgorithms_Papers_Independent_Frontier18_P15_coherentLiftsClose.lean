-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P15.coherentLiftsClose
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T19:18:19.303748+00:00
-- url     : https://prove2.me/submissions/82540c13-0d08-432b-8443-22f1713ddc5d

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P15

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

open scoped Matrix ComplexConjugate BigOperators

namespace X6F15

open QAlgorithms

variable {J : Type} [Fintype J] [DecidableEq J]

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

namespace X6F15

open QAlgorithms

variable {J : Type} [Fintype J] [DecidableEq J]

lemma inner_unitary (U : Matrix J J ℂ) (hU : star U * U = 1) (x y : J → ℂ) :
    ∑ a, (U *ᵥ x) a * conj ((U *ᵥ y) a) = ∑ i, x i * conj (y i) := by
  have h1 : ∑ a, (U *ᵥ x) a * conj ((U *ᵥ y) a) = (star (U *ᵥ y)) ⬝ᵥ (U *ᵥ x) := by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def]
    exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  rw [h1, Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, hU, Matrix.vecMul_one]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)

lemma hellinger {d : ℕ} (p q : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpSum : ∑ i, p i = 1) (hqSum : ∑ i, q i = 1) :
    1 - (∑ i, Real.sqrt (p i) * Real.sqrt (q i)) ^ 2 ≤ ∑ i, |p i - q i| := by
  set B := ∑ i, Real.sqrt (p i) * Real.sqrt (q i)
  have h1 : ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 = 2 - 2 * B := by
    have e : ∀ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 =
        p i + q i - 2 * (Real.sqrt (p i) * Real.sqrt (q i)) := by
      intro i
      rw [sub_sq, Real.sq_sqrt (hp i), Real.sq_sqrt (hq i)]; ring
    rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      hpSum, hqSum, ← Finset.mul_sum]
    ring
  have h2 : ∀ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2 ≤ |p i - q i| := by
    intro i
    have hpq : p i - q i = (Real.sqrt (p i) - Real.sqrt (q i)) * (Real.sqrt (p i) + Real.sqrt (q i)) := by
      have := Real.sq_sqrt (hp i); have := Real.sq_sqrt (hq i)
      nlinarith
    rw [hpq, abs_mul, sq, ← abs_mul_abs_self]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (p i) + Real.sqrt (q i))]
    rw [abs_le]; constructor <;> nlinarith [Real.sqrt_nonneg (p i), Real.sqrt_nonneg (q i)]
  have h3 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h2 i)
  rw [h1] at h3
  nlinarith [sq_nonneg (1 - B)]

end X6F15

open QAlgorithms QAlgorithms.Papers.Independent.Frontier18.P15

theorem solution (d : ℕ) (hd : 0 < d)
    (p q : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpSum : ∑ i, p i = 1) (hqSum : ∑ i, q i = 1)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hclose : traceNorm
      (conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) (Matrix.diagonal fun i => (p i : ℂ)) -
       conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) (Matrix.diagonal fun i => (q i : ℂ))) ≤
      epsilon) :
    traceNorm
      (pureDensity (act (U : Matrix (Fin d) (Fin d) ℂ) (coherentLift p)) -
       pureDensity (act (U : Matrix (Fin d) (Fin d) ℂ) (coherentLift q))) ≤
      2 * Real.sqrt epsilon := by
  have hU1 : star (U : Matrix (Fin d) (Fin d) ℂ) * U = 1 := Unitary.star_mul_self_of_mem U.2
  have hU2 : (U : Matrix (Fin d) (Fin d) ℂ) * star (U : Matrix (Fin d) (Fin d) ℂ) = 1 :=
    Unitary.mul_star_self_of_mem U.2
  -- lower bound for the classical distance
  have hdiff : conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) (Matrix.diagonal fun i => (p i : ℂ)) -
       conjSuperop (U : Matrix (Fin d) (Fin d) ℂ) (Matrix.diagonal fun i => (q i : ℂ)) =
      (U : Matrix (Fin d) (Fin d) ℂ) * Matrix.diagonal (fun i => ((p i - q i : ℝ) : ℂ)) *
        star (U : Matrix (Fin d) (Fin d) ℂ) := by
    rw [conjSuperop, conjSuperop, ← Matrix.star_eq_conjTranspose, ← Matrix.sub_mul, ← Matrix.mul_sub,
      Matrix.diagonal_sub]
    congr 3; funext i; push_cast; ring
  have hTV : ∑ i, |p i - q i| ≤ epsilon := by
    have := X6F15.tn_lower (U : Matrix (Fin d) (Fin d) ℂ) hU1 hU2 (fun i => p i - q i)
    rw [← hdiff] at this
    linarith
  set B := ∑ i, Real.sqrt (p i) * Real.sqrt (q i)
  have hc : ∀ (r : Fin d → ℝ), (∀ i, 0 ≤ r i) → ∀ (s : Fin d → ℝ), (∀ i, 0 ≤ s i) →
      ∑ a, (act (U : Matrix (Fin d) (Fin d) ℂ) (coherentLift r)) a *
        conj ((act (U : Matrix (Fin d) (Fin d) ℂ) (coherentLift s)) a) =
      ((∑ i, Real.sqrt (r i) * Real.sqrt (s i) : ℝ) : ℂ) := by
    intro r hr s hs
    have := X6F15.inner_unitary (U : Matrix (Fin d) (Fin d) ℂ) hU1
      (fun i => (Real.sqrt (r i) : ℂ)) (fun i => (Real.sqrt (s i) : ℂ))
    simp only [act, coherentLift] at this ⊢
    rw [this]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Complex.conj_ofReal]
  have hnorm : ∀ (r : Fin d → ℝ), (∀ i, 0 ≤ r i) → ∑ i, r i = 1 →
      ∑ a, (act (U : Matrix (Fin d) (Fin d) ℂ) (coherentLift r)) a *
        conj ((act (U : Matrix (Fin d) (Fin d) ℂ) (coherentLift r)) a) = 1 := by
    intro r hr hrs
    rw [hc r hr r hr]
    have : ∑ i, Real.sqrt (r i) * Real.sqrt (r i) = 1 := by
      rw [← hrs]; exact Finset.sum_congr rfl (fun i _ => Real.mul_self_sqrt (hr i))
    rw [this]; simp
  have hpure := X6F15.tn_pure _ _ (hnorm p hp hpSum) (hnorm q hq hqSum) B (hc p hp q hq)
  have hH := X6F15.hellinger p q hp hq hpSum hqSum
  calc _ ≤ 2 * Real.sqrt (1 - B ^ 2) := hpure
    _ ≤ 2 * Real.sqrt epsilon := by
      have := Real.sqrt_le_sqrt (le_trans hH hTV)
      linarith
