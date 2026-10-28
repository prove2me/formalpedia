-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P42.massiveAction_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T04:55:29.329995+00:00
-- url     : https://prove2.me/submissions/7c192b67-b78f-474b-8cbb-83f2e3860a6a

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators Interval Topology

open Filter Set MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

lemma mink_norm_fourFlow (c : ℝ) (u : V3) (hc : 0 < c) (hu : dot3 u u < c ^ 2) :
    (fourFlow c u 0) ^ 2 - (fourFlow c u 1) ^ 2 - (fourFlow c u 2) ^ 2 - (fourFlow c u 3) ^ 2 = 1 := by
  have h1 : 0 < 1 - dot3 u u / c ^ 2 := by
    have : dot3 u u / c ^ 2 < 1 := by rw [div_lt_one (by positivity)]; exact hu
    linarith
  have hg : (lorentzFactor c u) ^ 2 * (1 - dot3 u u / c ^ 2) = 1 := by
    unfold lorentzFactor
    rw [div_pow, Real.sq_sqrt h1.le]
    have : (1 - dot3 u u / c ^ 2) ≠ 0 := h1.ne'
    rw [one_pow, div_mul_cancel₀ _ this]
  simp only [fourFlow, dot3, Fin.sum_univ_three] at hg ⊢
  simp
  field_simp
  field_simp at hg
  nlinarith [hg]


lemma mink_sq (i j : Fin 4) :
    ∑ k, minkowskiMetric i k * minkowskiMetric k j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [minkowskiMetric]

lemma mink_apply (W : V4) (i : Fin 4) :
    ∑ k, minkowskiMetric i k * apply4 minkowskiMetric W k = W i := by
  fin_cases i <;> simp [Fin.sum_univ_four, minkowskiMetric, apply4]

lemma mink_apply' (W : V4) (j : Fin 4) :
    ∑ k, W k * minkowskiMetric k j = apply4 minkowskiMetric W j := by
  fin_cases j <;> simp [Fin.sum_univ_four, minkowskiMetric, apply4]

lemma mink_self (W : V4) (hW : W 0 ^ 2 - W 1 ^ 2 - W 2 ^ 2 - W 3 ^ 2 = 1) :
    ∑ k, W k * apply4 minkowskiMetric W k = 1 := by
  simp [Fin.sum_univ_four, minkowskiMetric, apply4]
  linear_combination hW

lemma gUp_mul_gDown_aux (n : ℝ) (hn : n ≠ 0) (W : V4)
    (hW : W 0 ^ 2 - W 1 ^ 2 - W 2 ^ 2 - W 3 ^ 2 = 1) (i j : Fin 4) :
    ∑ k, (minkowskiMetric i k + (n ^ 2 - 1) * W i * W k) *
      (minkowskiMetric k j + (1 / n ^ 2 - 1) *
        apply4 minkowskiMetric W k * apply4 minkowskiMetric W j) = if i = j then 1 else 0 := by
  have key : (1 / n ^ 2 - 1) + (n ^ 2 - 1) + (n ^ 2 - 1) * (1 / n ^ 2 - 1) = 0 := by
    field_simp; ring
  have : ∀ k, (minkowskiMetric i k + (n ^ 2 - 1) * W i * W k) *
      (minkowskiMetric k j + (1 / n ^ 2 - 1) *
        apply4 minkowskiMetric W k * apply4 minkowskiMetric W j) =
      minkowskiMetric i k * minkowskiMetric k j +
      ((1 / n ^ 2 - 1) * apply4 minkowskiMetric W j) * (minkowskiMetric i k * apply4 minkowskiMetric W k) +
      ((n ^ 2 - 1) * W i) * (W k * minkowskiMetric k j) +
      ((n ^ 2 - 1) * (1 / n ^ 2 - 1) * W i * apply4 minkowskiMetric W j) *
        (W k * apply4 minkowskiMetric W k) := by intro k; ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, mink_sq, mink_apply, mink_apply', mink_self W hW]
  linear_combination (W i * apply4 minkowskiMetric W j) * key

lemma cartesianPartial_eq_of_hasFDerivAt {d : ℕ} {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    {f' : (Fin d → ℝ) →L[ℝ] ℝ} (h : HasFDerivAt f f' x) (i : Fin d) :
    cartesianPartial f x i = f' (Pi.single i 1) := by
  unfold cartesianPartial QAlgorithms.Papers.Independent.Dependency50.P20.coordinatePartial
  have hL : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => (WithLp.ofLp y : Fin d → ℝ))
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap)
      (WithLp.toLp 2 x) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap.hasFDerivAt
  have h2 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => f (WithLp.ofLp y))
      (f'.comp ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap))
      (WithLp.toLp 2 x) := by
    have : HasFDerivAt f f' (WithLp.ofLp (WithLp.toLp 2 x)) := by simpa using h
    exact HasFDerivAt.comp (WithLp.toLp 2 x) this hL
  rw [h2.fderiv]
  simp
  congr 1


lemma flow_comp_contDiffOn {c : ℝ} (P : OpticalPatch c) (j : Fin 3) :
    ContDiffOn ℝ 2 (fun x => P.flow x j) P.domain :=
  (contDiffOn_pi.mp P.flowRegular) j

lemma lorentzFactor_contDiffOn {c : ℝ} (hc : 0 < c) (P : OpticalPatch c) :
    ContDiffOn ℝ 2 (fun x => lorentzFactor c (P.flow x)) P.domain := by
  unfold lorentzFactor
  have hd : ContDiffOn ℝ 2 (fun x => dot3 (P.flow x) (P.flow x)) P.domain := by
    unfold dot3
    exact ContDiffOn.sum (fun i _ => (flow_comp_contDiffOn P i).mul (flow_comp_contDiffOn P i))
  have h1 : ContDiffOn ℝ 2 (fun x => 1 - dot3 (P.flow x) (P.flow x) / c ^ 2) P.domain :=
    contDiffOn_const.sub (hd.div_const _)
  have h2 : ContDiffOn ℝ 2 (fun x => Real.sqrt (1 - dot3 (P.flow x) (P.flow x) / c ^ 2)) P.domain := by
    refine h1.sqrt ?_
    intro x hx
    have := P.flowBound x hx
    have : dot3 (P.flow x) (P.flow x) / c ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]; exact this
    linarith
  refine contDiffOn_const.div h2 ?_
  intro x hx
  have := P.flowBound x hx
  have : dot3 (P.flow x) (P.flow x) / c ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; exact this
  exact (Real.sqrt_pos.mpr (by linarith)).ne'

lemma fourFlow_contDiffOn {c : ℝ} (hc : 0 < c) (P : OpticalPatch c) (i : Fin 4) :
    ContDiffOn ℝ 2 (fun x => fourFlow c (P.flow x) i) P.domain := by
  have hg := lorentzFactor_contDiffOn hc P
  fin_cases i
  · simpa [fourFlow] using hg
  · simp only [fourFlow]
    exact ((hg.mul (flow_comp_contDiffOn P 0)).div_const c)
  · simp only [fourFlow]
    exact ((hg.mul (flow_comp_contDiffOn P 1)).div_const c)
  · simp only [fourFlow]
    exact ((hg.mul (flow_comp_contDiffOn P 2)).div_const c)


lemma apply4_contDiffOn_fourFlow {c : ℝ} (hc : 0 < c) (P : OpticalPatch c) (i : Fin 4) :
    ContDiffOn ℝ 2 (fun x => apply4 minkowskiMetric (fourFlow c (P.flow x)) i) P.domain := by
  unfold apply4
  exact ContDiffOn.sum (fun j _ => contDiffOn_const.mul (fourFlow_contDiffOn hc P j))

lemma patchDown_contDiffOn {c : ℝ} (hc : 0 < c) (P : OpticalPatch c) (a b : Fin 4) :
    ContDiffOn ℝ 2 (fun x => patchDown P x a b) P.domain := by
  unfold patchDown gDown
  have hn : ContDiffOn ℝ 2 (fun x => 1 / (P.index x) ^ 2 - 1) P.domain := by
    refine (contDiffOn_const.div (P.indexRegular.pow 2) ?_).sub contDiffOn_const
    intro x hx
    have := P.indexBound x hx
    positivity
  exact contDiffOn_const.add ((hn.mul (apply4_contDiffOn_fourFlow hc P a)).mul
    (apply4_contDiffOn_fourFlow hc P b))

lemma patchUp_contDiffOn {c : ℝ} (hc : 0 < c) (P : OpticalPatch c) (a b : Fin 4) :
    ContDiffOn ℝ 2 (fun x => patchUp P x a b) P.domain := by
  unfold patchUp gUp
  have hn : ContDiffOn ℝ 2 (fun x => (P.index x) ^ 2 - 1) P.domain :=
    (P.indexRegular.pow 2).sub contDiffOn_const
  exact contDiffOn_const.add ((hn.mul (fourFlow_contDiffOn hc P a)).mul
    (fourFlow_contDiffOn hc P b))

lemma mink_symm (a b : Fin 4) : minkowskiMetric a b = minkowskiMetric b a := by
  unfold minkowskiMetric
  by_cases h : a = b
  · subst h; rfl
  · simp [h, Ne.symm h]

lemma patchDown_symm {c : ℝ} (P : OpticalPatch c) (x : V4) (a b : Fin 4) :
    patchDown P x a b = patchDown P x b a := by
  unfold patchDown gDown
  rw [mink_symm a b]; ring

lemma patchUp_mul_patchDown {c : ℝ} (hc : 0 < c) (P : OpticalPatch c) (x : V4) (hx : x ∈ P.domain)
    (a b : Fin 4) :
    ∑ k, patchUp P x a k * patchDown P x k b = if a = b then 1 else 0 := by
  have hn : P.index x ≠ 0 := by have := P.indexBound x hx; positivity
  have := gUp_mul_gDown_aux (P.index x) hn (fourFlow c (P.flow x))
    (mink_norm_fourFlow c (P.flow x) hc (P.flowBound x hx)) a b
  simpa [patchUp, patchDown, gUp, gDown] using this

lemma patchDown_mul_patchUp {c : ℝ} (hc : 0 < c) (P : OpticalPatch c) (x : V4) (hx : x ∈ P.domain)
    (a b : Fin 4) :
    ∑ k, patchDown P x a k * patchUp P x k b = if a = b then 1 else 0 := by
  have h : patchUp P x * patchDown P x = 1 := by
    ext i j
    rw [Matrix.mul_apply, patchUp_mul_patchDown hc P x hx]
    simp [Matrix.one_apply]
  have h2 := mul_eq_one_comm.mp h
  have := congrFun (congrFun h2 a) b
  rw [Matrix.mul_apply] at this
  simpa [Matrix.one_apply] using this


lemma clm_apply_eq_sum {d : ℕ} (f' : (Fin d → ℝ) →L[ℝ] ℝ) (v : Fin d → ℝ) :
    f' v = ∑ c, v c * f' (Pi.single c 1) := by
  conv_lhs => rw [pi_eq_sum_univ v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [map_smul]
  have : (fun j : Fin d => if c = j then (1:ℝ) else 0) = Pi.single c 1 := by
    funext j; simp [Pi.single_apply, eq_comm]
  rw [this, smul_eq_mul]

lemma el_algebra (G Gi : Fin 4 → Fin 4 → ℝ) (hsymm : ∀ a b, G a b = G b a)
    (hinv : ∀ a b, ∑ k, G a k * Gi k b = if a = b then 1 else 0)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (hdg : ∀ c a b, dg c a b = dg c b a)
    (v acc : Fin 4 → ℝ)
    (hacc : ∀ a, acc a + ∑ b, ∑ d, (1 / 2 * ∑ e, Gi a e * (dg b e d + dg d e b - dg e b d)) *
      v b * v d = 0) (b : Fin 4) :
    ∑ a, ((∑ c, v c * dg c a b) * v a + G a b * acc a) =
      1 / 2 * ∑ c, ∑ d, dg b c d * v c * v d := by
  obtain ⟨S, hS⟩ : ∃ S : Fin 4 → ℝ, ∀ e, S e =
      ∑ c, ∑ d, (dg c e d + dg d e c - dg e c d) * v c * v d := ⟨_, fun e => rfl⟩
  have h1 : ∀ a, acc a = -(1 / 2) * ∑ e, Gi a e * S e := by
    intro a
    have := hacc a
    have h' : ∑ b, ∑ d, (1 / 2 * ∑ e, Gi a e * (dg b e d + dg d e b - dg e b d)) * v b * v d =
        1 / 2 * ∑ e, Gi a e * S e := by
      simp only [hS, Fin.sum_univ_four]; ring
    linarith
  have hb : ∀ e, ∑ a, G a b * Gi a e = if b = e then 1 else 0 := by
    intro e
    rw [← hinv b e]
    exact Finset.sum_congr rfl (fun a _ => by rw [hsymm a b])
  have h2 : ∑ a, G a b * acc a = -(1 / 2) * S b := by
    have : ∑ a, G a b * acc a = -(1 / 2) * ∑ e, (∑ a, G a b * Gi a e) * S e := by
      simp only [h1, Fin.sum_univ_four]; ring
    rw [this]
    simp [hb]
  have hT1 : ∑ a, (∑ c, v c * dg c a b) * v a = ∑ c, ∑ d, dg c b d * v c * v d := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => ?_))
    rw [hdg c d b]; ring
  have hT2 : ∑ c, ∑ d, dg d b c * v c * v d = ∑ c, ∑ d, dg c b d * v c * v d := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun d _ => by ring))
  have hSb : S b = 2 * ∑ c, ∑ d, dg c b d * v c * v d - ∑ c, ∑ d, dg b c d * v c * v d := by
    rw [hS]
    simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hT2]; ring
  rw [Finset.sum_add_distrib, h2, hT1, hSb]
  ring

lemma el_algebra2 (G Gi : Fin 4 → Fin 4 → ℝ) (hinv : ∀ a b, ∑ k, G a k * Gi k b = if a = b then 1 else 0)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (hdg : ∀ c a b, dg c a b = dg c b a)
    (v acc : Fin 4 → ℝ)
    (hacc : ∀ a, acc a + ∑ b, ∑ d, (1 / 2 * ∑ e, Gi a e * (dg b e d + dg d e b - dg e b d)) *
      v b * v d = 0) :
    ∑ b, ((1 / 2 * ∑ c, ∑ d, dg b c d * v c * v d) * v b + (∑ a, G a b * v a) * acc b) = 0 := by
  obtain ⟨S, hS⟩ : ∃ S : Fin 4 → ℝ, ∀ e, S e =
      ∑ c, ∑ d, (dg c e d + dg d e c - dg e c d) * v c * v d := ⟨_, fun e => rfl⟩
  have h1 : ∀ a, acc a = -(1 / 2) * ∑ e, Gi a e * S e := by
    intro a
    have := hacc a
    have h' : ∑ b, ∑ d, (1 / 2 * ∑ e, Gi a e * (dg b e d + dg d e b - dg e b d)) * v b * v d =
        1 / 2 * ∑ e, Gi a e * S e := by
      simp only [hS, Fin.sum_univ_four]; ring
    linarith
  have h2 : ∑ b, (∑ a, G a b * v a) * acc b = -(1 / 2) * ∑ a, v a * S a := by
    have : ∑ b, (∑ a, G a b * v a) * acc b =
        -(1 / 2) * ∑ e, (∑ a, v a * (∑ b, G a b * Gi b e)) * S e := by
      simp only [h1, Fin.sum_univ_four]; ring
    rw [this]
    simp only [hinv]
    simp [mul_ite, Finset.sum_ite_eq]
  have hX : ∑ a, v a * S a = ∑ a, ∑ c, ∑ d, dg a c d * v a * v c * v d := by
    have : ∀ a, v a * S a = ∑ c, ∑ d, (dg c a d * (v a * v c * v d) + dg d c a * (v a * v c * v d)
        - dg a c d * (v a * v c * v d)) := by
      intro a
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [hdg d a c]; ring
    simp only [this, Fin.sum_univ_four]; ring
  have hY : ∑ b, (1 / 2 * ∑ c, ∑ d, dg b c d * v c * v d) * v b =
      1 / 2 * ∑ a, ∑ c, ∑ d, dg a c d * v a * v c * v d := by
    simp only [Fin.sum_univ_four]; ring
  rw [Finset.sum_add_distrib, h2, hX, hY]
  ring

lemma el_hasDerivAt {g gi : V4 → M4} {D : Set V4} {J : Set ℝ} (hD : IsOpen D) (hJ : IsOpen J)
    (hg : ∀ a b, ContDiffOn ℝ 2 (fun x => g x a b) D) (hsymm : ∀ x a b, g x a b = g x b a)
    (hinv : ∀ x ∈ D, ∀ a b, ∑ k, g x a k * gi x k b = if a = b then 1 else 0)
    {γ : ℝ → V4} (hγ : ContDiffOn ℝ 2 γ J) {s : ℝ} (hs : s ∈ J) (hx : γ s ∈ D)
    (hacc : covAcceleration g gi γ s = 0) (b : Fin 4) :
    HasDerivAt (fun t => ∑ a, g (γ t) a b * deriv γ t a)
      (1 / 2 * ∑ c, ∑ d, cartesianPartial (fun y => g y c d) (γ s) b * deriv γ s c * deriv γ s d) s := by
  have hγd : HasDerivAt γ (deriv γ s) s :=
    ((hγ.differentiableOn (by norm_num)).differentiableAt (hJ.mem_nhds hs)).hasDerivAt
  have hdγ : ContDiffOn ℝ 1 (deriv γ) J := hγ.deriv_of_isOpen hJ (by norm_num)
  have hdd : HasDerivAt (deriv γ) (deriv (deriv γ) s) s :=
    ((hdγ.differentiableOn (by norm_num)).differentiableAt (hJ.mem_nhds hs)).hasDerivAt
  have hg' : ∀ a b, HasFDerivAt (fun x => g x a b) (fderiv ℝ (fun x => g x a b) (γ s)) (γ s) :=
    fun a b => (((hg a b).contDiffAt (hD.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
  have hterm : ∀ a, HasDerivAt (fun t => g (γ t) a b * deriv γ t a)
      (fderiv ℝ (fun x => g x a b) (γ s) (deriv γ s) * deriv γ s a +
        g (γ s) a b * deriv (deriv γ) s a) s := by
    intro a
    exact ((hg' a b).comp_hasDerivAt s hγd).mul (hasDerivAt_pi.mp hdd a)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun a _ => hterm a)
  refine hsum.congr_deriv ?_
  -- algebra
  set v := deriv γ s with hv
  set acc := deriv (deriv γ) s with hacc'
  set x := γ s with hxdef
  set dg : Fin 4 → Fin 4 → Fin 4 → ℝ := fun c a b => cartesianPartial (fun y => g y a b) x c with hdg
  have hdg_eq : ∀ c a b, fderiv ℝ (fun y => g y a b) x (Pi.single c 1) = dg c a b := by
    intro c a b
    rw [hdg]; simp only
    rw [cartesianPartial_eq_of_hasFDerivAt (hg' a b)]
  have hdg_symm : ∀ c a b, dg c a b = dg c b a := by
    intro c a b
    simp only [hdg]
    have : (fun y => g y a b) = (fun y => g y b a) := funext (fun y => hsymm y a b)
    rw [this]
  have hfd : ∀ a, fderiv ℝ (fun y => g y a b) x v = ∑ c, v c * dg c a b := by
    intro a
    rw [clm_apply_eq_sum]
    exact Finset.sum_congr rfl (fun c _ => by rw [hdg_eq])
  have hacc2 : ∀ a, acc a + ∑ b, ∑ d, (1 / 2 * ∑ e, gi x a e * (dg b e d + dg d e b - dg e b d)) *
      v b * v d = 0 := by
    intro a
    have h := congrFun hacc a
    simp only [covAcceleration, Pi.zero_apply] at h
    have hd : deriv (fun t => deriv γ t a) s = acc a := (hasDerivAt_pi.mp hdd a).deriv
    rw [hd] at h
    exact h
  have key := el_algebra (fun a b => g x a b) (fun a b => gi x a b) (hsymm x) (hinv x hx) dg
    hdg_symm v acc hacc2 b
  simp only [hfd]
  exact key


lemma el_Q_hasDerivAt {g gi : V4 → M4} {D : Set V4} {J : Set ℝ} (hD : IsOpen D) (hJ : IsOpen J)
    (hg : ∀ a b, ContDiffOn ℝ 2 (fun x => g x a b) D) (hsymm : ∀ x a b, g x a b = g x b a)
    (hinv : ∀ x ∈ D, ∀ a b, ∑ k, g x a k * gi x k b = if a = b then 1 else 0)
    {γ : ℝ → V4} (hγ : ContDiffOn ℝ 2 γ J) {s : ℝ} (hs : s ∈ J) (hx : γ s ∈ D)
    (hacc : covAcceleration g gi γ s = 0) :
    HasDerivAt (fun t => quadratic (g (γ t)) (deriv γ t)) 0 s := by
  have hγd : HasDerivAt γ (deriv γ s) s :=
    ((hγ.differentiableOn (by norm_num)).differentiableAt (hJ.mem_nhds hs)).hasDerivAt
  have hdγ : ContDiffOn ℝ 1 (deriv γ) J := hγ.deriv_of_isOpen hJ (by norm_num)
  have hdd : HasDerivAt (deriv γ) (deriv (deriv γ) s) s :=
    ((hdγ.differentiableOn (by norm_num)).differentiableAt (hJ.mem_nhds hs)).hasDerivAt
  have hp : ∀ b, HasDerivAt (fun t => ∑ a, g (γ t) a b * deriv γ t a)
      (1 / 2 * ∑ c, ∑ d, cartesianPartial (fun y => g y c d) (γ s) b * deriv γ s c * deriv γ s d) s :=
    fun b => el_hasDerivAt hD hJ hg hsymm hinv hγ hs hx hacc b
  have hterm : ∀ b, HasDerivAt (fun t => (∑ a, g (γ t) a b * deriv γ t a) * deriv γ t b)
      ((1 / 2 * ∑ c, ∑ d, cartesianPartial (fun y => g y c d) (γ s) b * deriv γ s c * deriv γ s d)
        * deriv γ s b + (∑ a, g (γ s) a b * deriv γ s a) * deriv (deriv γ) s b) s :=
    fun b => (hp b).mul (hasDerivAt_pi.mp hdd b)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun b _ => hterm b)
  have hfun : (fun t => quadratic (g (γ t)) (deriv γ t)) =
      fun t => ∑ b, (∑ a, g (γ t) a b * deriv γ t a) * deriv γ t b := by
    funext t
    unfold quadratic
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  rw [hfun]
  refine hsum.congr_deriv ?_
  set v := deriv γ s with hv
  set acc := deriv (deriv γ) s with hacc'
  set x := γ s with hxdef
  set dg : Fin 4 → Fin 4 → Fin 4 → ℝ := fun c a b => cartesianPartial (fun y => g y a b) x c with hdg
  have hg' : ∀ a b, HasFDerivAt (fun x => g x a b) (fderiv ℝ (fun x => g x a b) x) x :=
    fun a b => (((hg a b).contDiffAt (hD.mem_nhds hx)).differentiableAt (by norm_num)).hasFDerivAt
  have hdg_symm : ∀ c a b, dg c a b = dg c b a := by
    intro c a b
    simp only [hdg]
    have : (fun y => g y a b) = (fun y => g y b a) := funext (fun y => hsymm y a b)
    rw [this]
  have hacc2 : ∀ a, acc a + ∑ b, ∑ d, (1 / 2 * ∑ e, gi x a e * (dg b e d + dg d e b - dg e b d)) *
      v b * v d = 0 := by
    intro a
    have h := congrFun hacc a
    simp only [covAcceleration, Pi.zero_apply] at h
    have hd : deriv (fun t => deriv γ t a) s = acc a := (hasDerivAt_pi.mp hdd a).deriv
    rw [hd] at h
    exact h
  exact el_algebra2 (fun a b => g x a b) (fun a b => gi x a b) (hinv x hx) dg
    hdg_symm v acc hacc2



lemma lam_hasFDerivAt {g : V4 → M4} {x v : V4} {G' : Fin 4 → Fin 4 → V4 →L[ℝ] ℝ}
    (hg' : ∀ a b, HasFDerivAt (fun y => g y a b) (G' a b) x) :
    ∃ L : V4 × V4 →L[ℝ] ℝ, HasFDerivAt (fun p : V4 × V4 => quadratic (g p.1) p.2) L (x, v) ∧
      ∀ ξ η, L (ξ, η) = ∑ a, ∑ b, ((G' a b ξ) * v a * v b + η a * g x a b * v b +
        v a * g x a b * η b) := by
  have hv : ∀ a, HasFDerivAt (fun p : V4 × V4 => p.2 a)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) a).comp
        (ContinuousLinearMap.snd ℝ V4 V4)) (x, v) := fun a =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) a).hasFDerivAt).comp (x, v)
      (hasFDerivAt_snd)
  have hgp : ∀ a b, HasFDerivAt (fun p : V4 × V4 => g p.1 a b)
      ((G' a b).comp (ContinuousLinearMap.fst ℝ V4 V4)) (x, v) := fun a b => by
    have h1 : HasFDerivAt (fun y => g y a b) (G' a b) ((x, v).1) := hg' a b
    exact h1.comp (x, v) (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, v)))
  have hterm := fun a b => ((hv a).mul (hgp a b)).mul (hv b)
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun b _ => hterm a b))
  refine ⟨_, hsum, ?_⟩
  intro ξ η
  simp
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  ring


/-- Total map of the family. -/
def PhiF (q : ℝ → V4 → V4) : ℝ × V4 → V4 := fun p => q p.1 p.2

/-- Tangent along the family. -/
def PsiF (q : ℝ → V4 → V4) : ℝ × V4 → V4 := fun p => fderiv ℝ (PhiF q) p ((1 : ℝ), (0 : V4))

def RF (g : V4 → M4) (q : ℝ → V4 → V4) : ℝ × V4 → ℝ :=
  fun p => quadratic (g (PhiF q p)) (PsiF q p)

section
variable {q : ℝ → V4 → V4} {J : Set ℝ} {E : Set V4}

lemma phi_contDiffOn (hJ : IsOpen J) (hE : IsOpen E)
    (hq : ContDiffOn ℝ 2 (fun a : ℝ × V4 => q a.1 a.2) (J ×ˢ E)) :
    ContDiffOn ℝ 2 (PhiF q) (J ×ˢ E) := hq

lemma dphi_contDiffOn (hJ : IsOpen J) (hE : IsOpen E)
    (hq : ContDiffOn ℝ 2 (fun a : ℝ × V4 => q a.1 a.2) (J ×ˢ E)) :
    ContDiffOn ℝ 1 (fun p => fderiv ℝ (PhiF q) p) (J ×ˢ E) :=
  hq.fderiv_of_isOpen (hJ.prod hE) (by norm_num)

lemma psi_contDiffOn (hJ : IsOpen J) (hE : IsOpen E)
    (hq : ContDiffOn ℝ 2 (fun a : ℝ × V4 => q a.1 a.2) (J ×ˢ E)) :
    ContDiffOn ℝ 1 (PsiF q) (J ×ˢ E) :=
  (dphi_contDiffOn hJ hE hq).clm_apply contDiffOn_const

lemma psi_eq_deriv (hJ : IsOpen J) (hE : IsOpen E)
    (hq : ContDiffOn ℝ 2 (fun a : ℝ × V4 => q a.1 a.2) (J ×ˢ E))
    {s : ℝ} {y : V4} (hs : s ∈ J) (hy : y ∈ E) :
    HasDerivAt (fun t => q t y) (PsiF q (s, y)) s := by
  have hdiff : DifferentiableAt ℝ (PhiF q) (s, y) :=
    ((phi_contDiffOn hJ hE hq).differentiableOn (by norm_num)).differentiableAt
      ((hJ.prod hE).mem_nhds (Set.mk_mem_prod hs hy))
  have h1 : HasDerivAt (fun t : ℝ => ((t, y) : ℝ × V4)) ((1 : ℝ), (0 : V4)) s := by
    exact (hasDerivAt_id s).prodMk (hasDerivAt_const s y)
  have h2 := hdiff.hasFDerivAt.comp_hasDerivAt s h1
  exact h2


variable {g : V4 → M4} {D : Set V4}

def Wset (g : V4 → M4) (D : Set V4) (q : ℝ → V4 → V4) (J : Set ℝ) (E : Set V4) : Set (ℝ × V4) :=
  {p | p ∈ J ×ˢ E ∧ PhiF q p ∈ D ∧ 0 < RF g q p}

lemma R_contDiffOn (hJ : IsOpen J) (hE : IsOpen E) (hD : IsOpen D)
    (hg : ∀ a b, ContDiffOn ℝ 2 (fun x => g x a b) D)
    (hq : ContDiffOn ℝ 2 (fun a : ℝ × V4 => q a.1 a.2) (J ×ˢ E)) :
    ContDiffOn ℝ 1 (RF g q) ((J ×ˢ E) ∩ PhiF q ⁻¹' D) := by
  have hN : IsOpen (J ×ˢ E) := hJ.prod hE
  have hphi : ContDiffOn ℝ 1 (PhiF q) ((J ×ˢ E) ∩ PhiF q ⁻¹' D) :=
    ((phi_contDiffOn hJ hE hq).of_le (by norm_num)).mono inter_subset_left
  have hpsi : ContDiffOn ℝ 1 (PsiF q) ((J ×ˢ E) ∩ PhiF q ⁻¹' D) :=
    (psi_contDiffOn hJ hE hq).mono inter_subset_left
  unfold RF quadratic
  refine ContDiffOn.sum (fun a _ => ContDiffOn.sum (fun b _ => ?_))
  have h1 : ContDiffOn ℝ 1 (fun p => g (PhiF q p) a b) ((J ×ˢ E) ∩ PhiF q ⁻¹' D) :=
    ((hg a b).of_le (by norm_num)).comp hphi (fun p hp => hp.2)
  exact ((contDiffOn_pi.mp hpsi a).mul h1).mul (contDiffOn_pi.mp hpsi b)

lemma W_open (hJ : IsOpen J) (hE : IsOpen E) (hD : IsOpen D)
    (hg : ∀ a b, ContDiffOn ℝ 2 (fun x => g x a b) D)
    (hq : ContDiffOn ℝ 2 (fun a : ℝ × V4 => q a.1 a.2) (J ×ˢ E)) :
    IsOpen (Wset g D q J E) := by
  have hN : IsOpen (J ×ˢ E) := hJ.prod hE
  have h1 : IsOpen ((J ×ˢ E) ∩ PhiF q ⁻¹' D) :=
    (phi_contDiffOn hJ hE hq).continuousOn.isOpen_inter_preimage hN hD
  have h2 := (R_contDiffOn hJ hE hD hg hq).continuousOn.isOpen_inter_preimage h1 (isOpen_Ioi (a := (0:ℝ)))
  have : Wset g D q J E = (J ×ˢ E ∩ PhiF q ⁻¹' D) ∩ RF g q ⁻¹' Ioi 0 := by
    ext p
    simp only [Wset, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioi]
    tauto
  rw [this]; exact h2

lemma F_contDiffOn (hJ : IsOpen J) (hE : IsOpen E) (hD : IsOpen D)
    (hg : ∀ a b, ContDiffOn ℝ 2 (fun x => g x a b) D)
    (hq : ContDiffOn ℝ 2 (fun a : ℝ × V4 => q a.1 a.2) (J ×ˢ E)) :
    ContDiffOn ℝ 1 (fun p => Real.sqrt (RF g q p)) (Wset g D q J E) := by
  refine ContDiffOn.sqrt ((R_contDiffOn hJ hE hD hg hq).mono ?_) ?_
  · intro p hp; exact ⟨hp.1, hp.2.1⟩
  · intro p hp; exact hp.2.2.ne'

lemma mem_W (hJ : IsOpen J) (hE : IsOpen E)
    (hq : ContDiffOn ℝ 2 (fun a : ℝ × V4 => q a.1 a.2) (J ×ˢ E))
    {s : ℝ} {y : V4} (hs : s ∈ J) (hy : y ∈ E) (him : q s y ∈ D)
    (htime : 0 < quadratic (g (q s y)) (deriv (fun t => q t y) s)) :
    (s, y) ∈ Wset g D q J E := by
  refine ⟨Set.mk_mem_prod hs hy, him, ?_⟩
  rw [(psi_eq_deriv hJ hE hq hs hy).deriv] at htime
  exact htime

end

lemma param_integral_hasFDerivAt {Fsq : ℝ × V4 → ℝ} {W : Set (ℝ × V4)} {E : Set V4} {z : V4}
    (hW : IsOpen W) (hF : ContDiffOn ℝ 1 Fsq W) (hE : IsOpen E) (hz : z ∈ E)
    (hKW : Icc (0 : ℝ) 1 ×ˢ E ⊆ W) :
    HasFDerivAt (fun y => ∫ s in (0 : ℝ)..1, Fsq (s, y))
      (∫ s in (0 : ℝ)..1, (fderiv ℝ Fsq (s, z)).comp (ContinuousLinearMap.inr ℝ ℝ V4)) z := by
  obtain ⟨r, hr, hrE⟩ := Metric.isOpen_iff.mp hE z hz
  set r' := r / 2 with hr'
  have hr'pos : 0 < r' := by positivity
  have hball : Metric.closedBall z r' ⊆ E := fun y hy =>
    hrE (by rw [Metric.mem_ball]; exact lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (by linarith))
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall z r') :=
    isCompact_Icc.prod (isCompact_closedBall z r')
  have hKW' : Icc (0 : ℝ) 1 ×ˢ Metric.closedBall z r' ⊆ W :=
    (Set.prod_mono subset_rfl hball).trans hKW
  have hFc : ContinuousOn Fsq W := hF.continuousOn
  have hdc : ContinuousOn (fun p => fderiv ℝ Fsq p) W := hF.continuousOn_fderiv_of_isOpen hW le_rfl
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hdc.mono hKW')
  have hdiffW : ∀ p ∈ W, HasFDerivAt Fsq (fderiv ℝ Fsq p) p := fun p hp =>
    ((hF.differentiableOn one_ne_zero).differentiableAt (hW.mem_nhds hp)).hasFDerivAt
  have hmeas : ∀ x ∈ E, AEStronglyMeasurable (fun t => Fsq (t, x)) (volume.restrict (Ι (0:ℝ) 1)) := by
    intro x hx
    have : ContinuousOn (fun t : ℝ => Fsq (t, x)) (Icc 0 1) :=
      hFc.comp (by fun_prop) (fun t ht => hKW (Set.mk_mem_prod ht hx))
    rw [Set.uIoc_of_le zero_le_one]
    exact (this.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hint : IntervalIntegrable (fun t => Fsq (t, z)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hFc.comp (by fun_prop) (fun t ht => hKW (Set.mk_mem_prod ht hz))
  have hmeas' : AEStronglyMeasurable (fun t => (fderiv ℝ Fsq (t, z)).comp (ContinuousLinearMap.inr ℝ ℝ V4))
      (volume.restrict (Ι (0:ℝ) 1)) := by
    have : ContinuousOn (fun t : ℝ => (fderiv ℝ Fsq (t, z)).comp (ContinuousLinearMap.inr ℝ ℝ V4)) (Icc 0 1) := by
      have h1 : ContinuousOn (fun t : ℝ => fderiv ℝ Fsq (t, z)) (Icc 0 1) :=
        hdc.comp (by fun_prop) (fun t ht => hKW (Set.mk_mem_prod ht hz))
      exact h1.clm_comp continuousOn_const
    rw [Set.uIoc_of_le zero_le_one]
    exact (this.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x t => Fsq (t, x))
    (F' := fun x t => (fderiv ℝ Fsq (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ V4))
    (bound := fun _ => C * 1) (s := Metric.ball z r') (Metric.ball_mem_nhds z hr'pos) ?_ hint hmeas' ?_
    intervalIntegrable_const ?_
  · filter_upwards [Metric.ball_mem_nhds z hr'pos] with x hx
    exact hmeas x (hball (Metric.ball_subset_closedBall hx))
  · refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hxb : x ∈ Metric.closedBall z r' := Metric.ball_subset_closedBall hx
    have h1 := hC (t, x) (Set.mk_mem_prod (Ioc_subset_Icc_self ht) hxb)
    calc ‖(fderiv ℝ Fsq (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ V4)‖
        ≤ ‖fderiv ℝ Fsq (t, x)‖ * ‖ContinuousLinearMap.inr ℝ ℝ V4‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * 1 := by
        gcongr
        · exact (norm_nonneg _).trans h1
        · exact ContinuousLinearMap.norm_inr_le_one ℝ ℝ V4
  · refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hxE : x ∈ E := hball (Metric.ball_subset_closedBall hx)
    have hp : (t, x) ∈ W := hKW (Set.mk_mem_prod (Ioc_subset_Icc_self ht) hxE)
    exact (hdiffW (t, x) hp).comp x (hasFDerivAt_prodMk_right t x)



lemma massiveLagrangian_eq (c n m : ℝ) (u v : V3) :
    massiveLagrangian c n m u v =
      -m * c * Real.sqrt (quadratic (gDown c n u) ![c, v 0, v 1, v 2]) := by
  unfold massiveLagrangian
  congr 2
  simp [quadratic, gDown, apply4, minkowskiMetric, fourFlow, Fin.sum_univ_four, dot3,
    Fin.sum_univ_three]
  ring

lemma dot3_smul_right (u k : V3) (l : ℝ) : dot3 u (l • k) = l * dot3 u k := by
  simp [dot3, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma dot3_smul_both (k : V3) (l : ℝ) : dot3 (l • k) (l • k) = l ^ 2 * dot3 k k := by
  simp [dot3, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma rayHamiltonian_smul (c n : ℝ) (u k : V3) {l : ℝ} (hl : 0 ≤ l) :
    rayHamiltonian c n u (l • k) = l * rayHamiltonian c n u k := by
  unfold rayHamiltonian
  rw [dot3_smul_both, dot3_smul_right]
  have : c ^ 2 * (l ^ 2 * dot3 k k) - ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) *
      (l * dot3 u k) ^ 2 = l ^ 2 * (c ^ 2 * dot3 k k - ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) *
      (dot3 u k) ^ 2) := by ring
  rw [this, Real.sqrt_mul (sq_nonneg l), Real.sqrt_sq hl]
  ring


lemma cs3 (u k : V3) : (dot3 u k) ^ 2 ≤ dot3 u u * dot3 k k := by
  simp only [dot3, Fin.sum_univ_three]
  nlinarith [sq_nonneg (u 0 * k 1 - u 1 * k 0), sq_nonneg (u 0 * k 2 - u 2 * k 0),
    sq_nonneg (u 1 * k 2 - u 2 * k 1)]

lemma dot3_self_pos {k : V3} (hk : k ≠ 0) : 0 < dot3 k k := by
  by_contra h
  have h := not_lt.mp h
  apply hk
  have h0 : dot3 k k = 0 := le_antisymm h (Finset.sum_nonneg (fun i _ => mul_self_nonneg _))
  simp only [dot3, Fin.sum_univ_three] at h0
  funext i
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (k 0), sq_nonneg (k 1), sq_nonneg (k 2)]

lemma ray_radicand_pos (c n : ℝ) (u k : V3) (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2)
    (hk : k ≠ 0) :
    0 < c ^ 2 * dot3 k k - ((n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u)) * (dot3 u k) ^ 2 := by
  have hn2 : 1 ≤ n ^ 2 := by nlinarith
  have hnc : 0 ≤ (n ^ 2 - 1) * c ^ 2 := mul_nonneg (sub_nonneg.2 hn2) (sq_nonneg c)
  have hden : 0 < n ^ 2 * c ^ 2 - dot3 u u := by nlinarith
  have hu0 : 0 ≤ dot3 u u := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hkk := dot3_self_pos hk
  have hb : 0 ≤ (n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u) :=
    div_nonneg (by nlinarith) hden.le
  have hbu : (n ^ 2 * c ^ 2 - c ^ 2) / (n ^ 2 * c ^ 2 - dot3 u u) * dot3 u u < c ^ 2 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [sq_nonneg c, mul_pos (by positivity : (0:ℝ) < n ^ 2) (sub_pos.mpr hu)]
  have h1 := mul_le_mul_of_nonneg_left (cs3 u k) hb
  nlinarith [mul_pos hkk (sub_pos.mpr hbu)]


lemma ray_differentiableAt (c n : ℝ) (u k : V3) (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2)
    (hk : k ≠ 0) : DifferentiableAt ℝ (rayHamiltonian c n u) k := by
  have hρ := ray_radicand_pos c n u k hc hn hu hk
  have hd1 : DifferentiableAt ℝ (fun k : V3 => dot3 u k) k := by
    unfold dot3; fun_prop
  have hd2 : DifferentiableAt ℝ (fun k : V3 => dot3 k k) k := by
    unfold dot3; fun_prop
  unfold rayHamiltonian
  refine DifferentiableAt.add (DifferentiableAt.mul (differentiableAt_const _) ?_) ?_
  · exact DifferentiableAt.sqrt (by fun_prop) hρ.ne'
  · exact DifferentiableAt.mul (differentiableAt_const _) hd1

lemma euler_ray (c n : ℝ) (u k : V3) (hc : 0 < c) (hn : 1 ≤ n) (hu : dot3 u u < c ^ 2)
    (hk : k ≠ 0) :
    dot3 k (rayVelocity c n u k) - rayHamiltonian c n u k = 0 := by
  have hd := ray_differentiableAt c n u k hc hn hu hk
  have h1 : HasDerivAt (fun l : ℝ => rayHamiltonian c n u (l • k))
      (fderiv ℝ (rayHamiltonian c n u) k k) 1 := by
    have h0 : HasDerivAt (fun l : ℝ => l • k) k 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const k
    have h0' : HasFDerivAt (rayHamiltonian c n u) (fderiv ℝ (rayHamiltonian c n u) k)
        ((fun l : ℝ => l • k) 1) := by simpa using hd.hasFDerivAt
    exact h0'.comp_hasDerivAt 1 h0
  have h2 : HasDerivAt (fun l : ℝ => rayHamiltonian c n u (l • k))
      (rayHamiltonian c n u k) 1 := by
    have hev : (fun l : ℝ => l * rayHamiltonian c n u k) =ᶠ[𝓝 1]
        fun l : ℝ => rayHamiltonian c n u (l • k) := by
      filter_upwards [Ioi_mem_nhds (zero_lt_one : (0:ℝ) < 1)] with l hl
      exact (rayHamiltonian_smul c n u k (le_of_lt hl)).symm
    have := ((hasDerivAt_id (1 : ℝ)).mul_const (rayHamiltonian c n u k)).congr_of_eventuallyEq hev.symm
    simpa using this
  have h3 : fderiv ℝ (rayHamiltonian c n u) k k = rayHamiltonian c n u k := h1.unique h2
  have h4 : dot3 k (rayVelocity c n u k) = fderiv ℝ (rayHamiltonian c n u) k k := by
    rw [clm_apply_eq_sum]
    unfold dot3 rayVelocity gradient
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [cartesianPartial_eq_of_hasFDerivAt hd.hasFDerivAt i]
  rw [h4, h3]; ring


lemma lam_alg (G : Fin 4 → Fin 4 → ℝ) (hsymm : ∀ a b, G a b = G b a)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) (W η v : Fin 4 → ℝ) :
    ∑ a, ∑ b, ((∑ c, W c * dg c a b) * v a * v b + η a * G a b * v b + v a * G a b * η b) =
      2 * ∑ b, (η b * (∑ a, G a b * v a) + W b * (1 / 2 * ∑ c, ∑ d, dg b c d * v c * v d)) := by
  have T2 : ∑ a, ∑ b, η a * G a b * v b = ∑ b, η b * (∑ a, G a b * v a) := by
    calc ∑ a, ∑ b, η a * G a b * v b = ∑ a, η a * ∑ b, G b a * v b := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun b _ => by rw [hsymm a b]; ring)
      _ = ∑ b, η b * (∑ a, G a b * v a) := rfl
  have T3 : ∑ a, ∑ b, v a * G a b * η b = ∑ b, η b * (∑ a, G a b * v a) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => by ring)
  have T1 : ∑ a, ∑ b, (∑ c, W c * dg c a b) * v a * v b =
      ∑ b, W b * (∑ c, ∑ d, dg b c d * v c * v d) := by
    simp only [Fin.sum_univ_four]; ring
  have hsplit : ∑ a, ∑ b, ((∑ c, W c * dg c a b) * v a * v b + η a * G a b * v b + v a * G a b * η b) =
      ∑ a, ∑ b, (∑ c, W c * dg c a b) * v a * v b + ∑ a, ∑ b, η a * G a b * v b +
        ∑ a, ∑ b, v a * G a b * η b := by
    simp only [Finset.sum_add_distrib]
  rw [hsplit, T1, T2, T3]
  simp only [Fin.sum_univ_four]; ring

structure GeoD (g gi : V4 → M4) (D : Set V4) : Prop where
  isOpen : IsOpen D
  smooth : ∀ a b, ContDiffOn ℝ 2 (fun x => g x a b) D
  symm : ∀ x a b, g x a b = g x b a
  inv : ∀ x ∈ D, ∀ a b, ∑ k, g x a k * gi x k b = if a = b then 1 else 0

structure FamD (g gi : V4 → M4) (D : Set V4) (q : ℝ → V4 → V4) (J : Set ℝ) (E : Set V4) : Prop where
  hJ : IsOpen J
  hE : IsOpen E
  h01 : Icc (0 : ℝ) 1 ⊆ J
  hq : ContDiffOn ℝ 2 (fun a : ℝ × V4 => q a.1 a.2) (J ×ˢ E)
  himage : ∀ y ∈ E, ∀ s ∈ Icc (0 : ℝ) 1, q s y ∈ D
  htime : ∀ y ∈ E, ∀ s ∈ Icc (0 : ℝ) 1,
    0 < quadratic (g (q s y)) (deriv (fun t => q t y) s)
  hgeo : ∀ y ∈ E, ∀ s ∈ Icc (0 : ℝ) 1,
    covAcceleration g gi (fun t => q t y) s = 0

section
variable {g gi : V4 → M4} {D : Set V4} {q : ℝ → V4 → V4} {J : Set ℝ} {E : Set V4}

lemma curve_contDiffOn (hF : FamD g gi D q J E) {y : V4} (hy : y ∈ E) :
    ContDiffOn ℝ 2 (fun t => q t y) J := by
  have h : ContDiffOn ℝ 2 (fun t : ℝ => ((t, y) : ℝ × V4)) J :=
    contDiffOn_id.prodMk contDiffOn_const
  exact hF.hq.comp h (fun t ht => Set.mk_mem_prod ht hy)

lemma Q_const (hG : GeoD g gi D) (hF : FamD g gi D q J E) {y : V4} (hy : y ∈ E) :
    ∀ s ∈ Icc (0 : ℝ) 1, quadratic (g (q s y)) (deriv (fun t => q t y) s) =
      quadratic (g (q 0 y)) (deriv (fun t => q t y) 0) := by
  have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt
      (fun t => quadratic (g (q t y)) (deriv (fun t => q t y) t)) 0 s := fun s hs =>
    el_Q_hasDerivAt hG.isOpen hF.hJ hG.smooth hG.symm hG.inv (curve_contDiffOn hF hy) (hF.h01 hs)
      (hF.himage y hy s hs) (hF.hgeo y hy s hs)
  have hcont : ContinuousOn (fun t => quadratic (g (q t y)) (deriv (fun t => q t y) t)) (Icc 0 1) :=
    fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
  exact constant_of_has_deriv_right_zero hcont
    (fun s hs => (hderiv s (Ico_subset_Icc_self hs)).hasDerivWithinAt)


lemma key_pointwise (hG : GeoD g gi D) (hF : FamD g gi D q J E) {z : V4} (hz : z ∈ E) (i : Fin 4)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun t => ∑ b, fderiv ℝ (PhiF q) (t, z) ((0 : ℝ), Pi.single i (1 : ℝ)) b *
        ∑ a, g (q t z) a b * deriv (fun τ => q τ z) t a)
      (Real.sqrt (RF g q (s, z)) *
        fderiv ℝ (fun p => Real.sqrt (RF g q p)) (s, z) ((0 : ℝ), Pi.single i (1 : ℝ))) s := by
  have hsJ : s ∈ J := hF.h01 hs
  have hN : IsOpen (J ×ˢ E) := hF.hJ.prod hF.hE
  have hmem : (s, z) ∈ J ×ˢ E := Set.mk_mem_prod hsJ hz
  set e : ℝ × V4 := ((0 : ℝ), Pi.single i (1 : ℝ)) with he
  set D1 := fderiv ℝ (PhiF q) with hD1def
  have hD1 : ContDiffOn ℝ 1 D1 (J ×ˢ E) := dphi_contDiffOn hF.hJ hF.hE hF.hq
  have hD1d : HasFDerivAt D1 (fderiv ℝ D1 (s, z)) (s, z) :=
    ((hD1.differentiableOn one_ne_zero).differentiableAt (hN.mem_nhds hmem)).hasFDerivAt
  have hPhid : HasFDerivAt (PhiF q) (D1 (s, z)) (s, z) :=
    (((phi_contDiffOn hF.hJ hF.hE hF.hq).differentiableOn (by norm_num)).differentiableAt
      (hN.mem_nhds hmem)).hasFDerivAt
  -- derivative of W
  have hWt : HasDerivAt (fun t => D1 (t, z) e) (fderiv ℝ D1 (s, z) ((1 : ℝ), (0 : V4)) e) s := by
    have h1 : HasDerivAt (fun t : ℝ => ((t, z) : ℝ × V4)) ((1 : ℝ), (0 : V4)) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s z)
    have h2 := hD1d.comp_hasDerivAt s h1
    have h3 := h2.clm_apply (hasDerivAt_const s e)
    simpa using h3
  have hWb : ∀ b, HasDerivAt (fun t => D1 (t, z) e b)
      (fderiv ℝ D1 (s, z) ((1 : ℝ), (0 : V4)) e b) s := fun b => hasDerivAt_pi.mp hWt b
  have hγ := curve_contDiffOn hF hz
  have hpb := fun b => el_hasDerivAt hG.isOpen hF.hJ hG.smooth hG.symm hG.inv hγ hsJ
    (hF.himage z hz s hs) (hF.hgeo z hz s hs) b
  have hG1 := HasDerivAt.fun_sum (u := Finset.univ) (fun b _ => (hWb b).mul (hpb b))
  have hPsid : HasFDerivAt (PsiF q) ((D1 (s, z)).comp (0 : ℝ × V4 →L[ℝ] ℝ × V4) +
      (fderiv ℝ D1 (s, z)).flip ((1 : ℝ), (0 : V4))) (s, z) := by
    have := hD1d.clm_apply (hasFDerivAt_const (((1 : ℝ), (0 : V4)) : ℝ × V4) (s, z))
    exact this
  have hWmem : (s, z) ∈ Wset g D q J E :=
    mem_W hF.hJ hF.hE hF.hq hsJ hz (hF.himage z hz s hs) (hF.htime z hz s hs)
  have hxD : PhiF q (s, z) ∈ D := hF.himage z hz s hs
  have hg'' : ∀ a b, HasFDerivAt (fun x => g x a b)
      (fderiv ℝ (fun x => g x a b) (PhiF q (s, z))) (PhiF q (s, z)) := fun a b =>
    (((hG.smooth a b).contDiffAt (hG.isOpen.mem_nhds hxD)).differentiableAt
      (by norm_num)).hasFDerivAt
  obtain ⟨L, hL, hLe⟩ := lam_hasFDerivAt (v := PsiF q (s, z)) hg''
  have hRd : HasFDerivAt (RF g q) (L.comp ((D1 (s, z)).prod ((D1 (s, z)).comp (0 : ℝ × V4 →L[ℝ] ℝ × V4) +
      (fderiv ℝ D1 (s, z)).flip ((1 : ℝ), (0 : V4))))) (s, z) := by
    have h1 := hPhid.prodMk hPsid
    exact HasFDerivAt.comp (g := fun w : V4 × V4 => quadratic (g w.1) w.2) (s, z) hL h1
  have hRpos : 0 < RF g q (s, z) := hWmem.2.2
  have hFd := hRd.sqrt hRpos.ne'
  have hsq : 0 < Real.sqrt (RF g q (s, z)) := Real.sqrt_pos.mpr hRpos
  rw [hFd.fderiv]
  refine hG1.congr_deriv ?_
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul, map_zero, zero_add]
  have hsymm2 : fderiv ℝ D1 (s, z) e ((1 : ℝ), (0 : V4)) = fderiv ℝ D1 (s, z) ((1 : ℝ), (0 : V4)) e :=
    ((phi_contDiffOn hF.hJ hF.hE hF.hq).contDiffAt (hN.mem_nhds hmem)).isSymmSndFDerivAt
      (by simp) e ((1 : ℝ), (0 : V4))
  have hfd : ∀ a b ξ, fderiv ℝ (fun x => g x a b) (PhiF q (s, z)) ξ =
      ∑ c, ξ c * cartesianPartial (fun y => g y a b) (q s z) c := by
    intro a b ξ
    rw [clm_apply_eq_sum]
    exact Finset.sum_congr rfl (fun c _ => by
      congr 1
      exact (cartesianPartial_eq_of_hasFDerivAt (hg'' a b) c).symm)
  have hpsi : PsiF q (s, z) = deriv (fun t => q t z) s :=
    (psi_eq_deriv hF.hJ hF.hE hF.hq hsJ hz).deriv.symm
  have hLval := hLe (D1 (s, z) e) (fderiv ℝ D1 (s, z) e ((1 : ℝ), (0 : V4)))
  simp only [hfd, hpsi] at hLval
  have halg := lam_alg (fun a b => g (q s z) a b) (hG.symm _)
    (fun c a b => cartesianPartial (fun y => g y a b) (q s z) c) (D1 (s, z) e)
    (fderiv ℝ D1 (s, z) ((1 : ℝ), (0 : V4)) e) (deriv (fun t => q t z) s)
  rw [hLval]
  have hPhi_eq : PhiF q (s, z) = q s z := rfl
  rw [hPhi_eq, hsymm2]
  rw [halg]
  field_simp
  ring


lemma end_values (hF : FamD g gi D q J E) {zBase : V4}
    (hend : ∀ y ∈ E, q 0 y = zBase ∧ q 1 y = y) {z : V4} (hz : z ∈ E) (i : Fin 4) :
    fderiv ℝ (PhiF q) ((0 : ℝ), z) ((0 : ℝ), Pi.single i (1 : ℝ)) = 0 ∧
    fderiv ℝ (PhiF q) ((1 : ℝ), z) ((0 : ℝ), Pi.single i (1 : ℝ)) = Pi.single i (1 : ℝ) := by
  have hN : IsOpen (J ×ˢ E) := hF.hJ.prod hF.hE
  have key : ∀ t0 : ℝ, t0 ∈ J → ∀ f : V4 → V4, (∀ y ∈ E, q t0 y = f y) → ∀ f' : V4 →L[ℝ] V4,
      HasFDerivAt f f' z →
      (fderiv ℝ (PhiF q) (t0, z)).comp (ContinuousLinearMap.inr ℝ ℝ V4) = f' := by
    intro t0 ht0 f hf f' hf'
    have hmem : (t0, z) ∈ J ×ˢ E := Set.mk_mem_prod ht0 hz
    have hPhid : HasFDerivAt (PhiF q) (fderiv ℝ (PhiF q) (t0, z)) (t0, z) :=
      (((phi_contDiffOn hF.hJ hF.hE hF.hq).differentiableOn (by norm_num)).differentiableAt
        (hN.mem_nhds hmem)).hasFDerivAt
    have h1 := hPhid.comp z (hasFDerivAt_prodMk_right t0 z)
    have h2 : HasFDerivAt f f' z := hf'
    have h3 : HasFDerivAt ((PhiF q) ∘ fun y : V4 => (t0, y)) _ z := h1
    have h4 : HasFDerivAt f ((fderiv ℝ (PhiF q) (t0, z)).comp (ContinuousLinearMap.inr ℝ ℝ V4)) z := by
      refine h3.congr_of_eventuallyEq ?_
      filter_upwards [hF.hE.mem_nhds hz] with y hy
      exact (hf y hy).symm
    exact h4.unique h2
  have h0 := key 0 (hF.h01 (by simp)) (fun _ => zBase) (fun y hy => (hend y hy).1) 0
    (hasFDerivAt_const _ _)
  have h1 := key 1 (hF.h01 (by simp)) id (fun y hy => (hend y hy).2) (ContinuousLinearMap.id ℝ V4)
    (hasFDerivAt_id _)
  refine ⟨?_, ?_⟩
  · have := congrArg (fun L => L (Pi.single i (1 : ℝ))) h0
    simpa using this
  · have := congrArg (fun L => L (Pi.single i (1 : ℝ))) h1
    simpa using this


lemma variation_main (hG : GeoD g gi D) (hF : FamD g gi D q J E) {zBase : V4}
    (hend : ∀ y ∈ E, q 0 y = zBase ∧ q 1 y = y) {z : V4} (hz : z ∈ E) (K : ℝ) :
    HasFDerivAt (fun y => K * ∫ s in (0 : ℝ)..1,
        Real.sqrt (quadratic (g (q s y)) (deriv (fun t => q t y) s)))
      (K • ∫ s in (0 : ℝ)..1, (fderiv ℝ (fun p => Real.sqrt (RF g q p)) (s, z)).comp
        (ContinuousLinearMap.inr ℝ ℝ V4)) z ∧
    ∀ i : Fin 4, (∫ s in (0 : ℝ)..1, (fderiv ℝ (fun p => Real.sqrt (RF g q p)) (s, z)).comp
        (ContinuousLinearMap.inr ℝ ℝ V4)) (Pi.single i (1 : ℝ)) =
      (∑ a, g z a i * deriv (fun t => q t z) 1 a) /
        Real.sqrt (quadratic (g z) (deriv (fun t => q t z) 1)) := by
  have hN : IsOpen (J ×ˢ E) := hF.hJ.prod hF.hE
  have hWo := W_open hF.hJ hF.hE hG.isOpen hG.smooth hF.hq
  have hKW : Icc (0 : ℝ) 1 ×ˢ E ⊆ Wset g D q J E := by
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    exact mem_W hF.hJ hF.hE hF.hq (hF.h01 hs) hy (hF.himage y hy s hs) (hF.htime y hy s hs)
  have hA := param_integral_hasFDerivAt hWo (F_contDiffOn hF.hJ hF.hE hG.isOpen hG.smooth hF.hq)
    hF.hE hz hKW
  have hRQ : ∀ y ∈ E, ∀ s ∈ Icc (0 : ℝ) 1, RF g q (s, y) =
      quadratic (g (q s y)) (deriv (fun t => q t y) s) := by
    intro y hy s hs
    unfold RF
    rw [← (psi_eq_deriv hF.hJ hF.hE hF.hq (hF.h01 hs) hy).deriv]
    rfl
  refine ⟨?_, ?_⟩
  · refine (hA.const_mul K).congr_of_eventuallyEq ?_
    filter_upwards [hF.hE.mem_nhds hz] with y hy
    congr 1
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [Set.uIcc_of_le zero_le_one] at hs
    rw [hRQ y hy s hs]
  · intro i
    set e : ℝ × V4 := ((0 : ℝ), Pi.single i (1 : ℝ)) with he
    have hQ := Q_const hG hF hz
    have hz1 : q 1 z = z := (hend z hz).2
    have hz0 := end_values hF hend hz i
    have hQ1 : 0 < quadratic (g (q 1 z)) (deriv (fun t => q t z) 1) := hF.htime z hz 1 (by simp)
    set L0 := Real.sqrt (quadratic (g (q 1 z)) (deriv (fun t => q t z) 1)) with hL0
    have hL0pos : 0 < L0 := Real.sqrt_pos.mpr hQ1
    have hsqR : ∀ s ∈ Icc (0 : ℝ) 1, Real.sqrt (RF g q (s, z)) = L0 := by
      intro s hs
      rw [hRQ z hz s hs, hQ s hs, hL0, hQ 1 (by simp)]
    -- the antiderivative
    set Gf : ℝ → ℝ := fun t => ∑ b, fderiv ℝ (PhiF q) (t, z) e b *
        ∑ a, g (q t z) a b * deriv (fun τ => q τ z) t a with hGf
    have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => Gf t / L0)
        (fderiv ℝ (fun p => Real.sqrt (RF g q p)) (s, z) e) s := by
      intro s hs
      rw [Set.uIcc_of_le zero_le_one] at hs
      have h1 := (key_pointwise hG hF hz i hs).div_const L0
      rw [hsqR s hs] at h1
      refine h1.congr_deriv ?_
      field_simp
      rfl
    have hcont : ContinuousOn (fun s : ℝ => fderiv ℝ (fun p => Real.sqrt (RF g q p)) (s, z) e)
        (Icc 0 1) := by
      have hdc : ContinuousOn (fun p => fderiv ℝ (fun p => Real.sqrt (RF g q p)) p) (Wset g D q J E) :=
        (F_contDiffOn hF.hJ hF.hE hG.isOpen hG.smooth hF.hq).continuousOn_fderiv_of_isOpen hWo le_rfl
      have h1 : ContinuousOn (fun s : ℝ => fderiv ℝ (fun p => Real.sqrt (RF g q p)) (s, z)) (Icc 0 1) :=
        hdc.comp (by fun_prop) (fun t ht => hKW (Set.mk_mem_prod ht hz))
      exact h1.clm_apply continuousOn_const
    have hint : IntervalIntegrable (fun s : ℝ => fderiv ℝ (fun p => Real.sqrt (RF g q p)) (s, z) e)
        volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rwa [Set.uIcc_of_le zero_le_one]
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hG0 : Gf 0 = 0 := by
      simp only [hGf, he, hz0.1]
      simp
    have hG1 : Gf 1 = ∑ a, g z a i * deriv (fun t => q t z) 1 a := by
      simp only [hGf, he, hz0.2, hz1]
      simp [Pi.single_apply]
    have hintCLM : IntervalIntegrable (fun s : ℝ => (fderiv ℝ (fun p => Real.sqrt (RF g q p)) (s, z)).comp
        (ContinuousLinearMap.inr ℝ ℝ V4)) volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le zero_le_one]
      have hdc : ContinuousOn (fun p => fderiv ℝ (fun p => Real.sqrt (RF g q p)) p) (Wset g D q J E) :=
        (F_contDiffOn hF.hJ hF.hE hG.isOpen hG.smooth hF.hq).continuousOn_fderiv_of_isOpen hWo le_rfl
      have h1 : ContinuousOn (fun s : ℝ => fderiv ℝ (fun p => Real.sqrt (RF g q p)) (s, z)) (Icc 0 1) :=
        hdc.comp (by fun_prop) (fun t ht => hKW (Set.mk_mem_prod ht hz))
      exact h1.clm_comp continuousOn_const
    rw [ContinuousLinearMap.intervalIntegral_apply hintCLM]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    rw [hftc]
    simp only [hG0, hG1, hz1]
    rw [zero_div, sub_zero, hL0, hz1]

end


lemma quad_up_massive {c : ℝ} (hc : 0 < c) (P : OpticalPatch c) (z : V4) (hz : z ∈ P.domain)
    (v : V4) (lam : ℝ) :
    quadratic (patchUp P z) (fun i => lam * apply4 (patchDown P z) v i) =
      lam ^ 2 * quadratic (patchDown P z) v := by
  have hA : ∀ i, ∑ j, patchUp P z i j * apply4 (patchDown P z) v j = v i := by
    intro i
    calc ∑ j, patchUp P z i j * apply4 (patchDown P z) v j
        = ∑ j, ∑ l, patchUp P z i j * (patchDown P z j l * v l) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          unfold apply4; rw [Finset.mul_sum]
      _ = ∑ l, (∑ j, patchUp P z i j * patchDown P z j l) * v l := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun l _ => ?_)
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = v i := by
          simp only [patchUp_mul_patchDown hc P z hz]
          simp
  have hQ : ∑ i, apply4 (patchDown P z) v i * v i = quadratic (patchDown P z) v := by
    unfold quadratic apply4
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  unfold quadratic
  have : ∀ i, ∑ j, (lam * apply4 (patchDown P z) v i) * patchUp P z i j * (lam * apply4 (patchDown P z) v j)
      = lam ^ 2 * (apply4 (patchDown P z) v i * ∑ j, patchUp P z i j * apply4 (patchDown P z) v j) := by
    intro i
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp only [this, hA]
  rw [← Finset.mul_sum]
  unfold quadratic at hQ
  rw [hQ]



end

end QAlgorithms.Papers.Independent.Renew46.P42

open scoped BigOperators

open Filter Set MeasureTheory

open QAlgorithms.Papers.Independent.Renew46.P42

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

theorem solution (c m : ℝ) (P : OpticalPatch c)
    (q : ℝ → V4 → V4) (z zBase : V4) (J : Set ℝ) (E : Set V4)
    (hc : 0 < c) (hm : 0 < m) (hz : z ∈ E)
    (hE : IsOpen E) (hEP : E ⊆ P.domain)
    (hJ : IsOpen J) (h01 : Icc (0 : ℝ) 1 ⊆ J)
    (hq : ContDiffOn ℝ 2 (fun a : ℝ × V4 => q a.1 a.2) (J ×ˢ E))
    (hend : ∀ y ∈ E, q 0 y = zBase ∧ q 1 y = y)
    (himage : ∀ y ∈ E, ∀ s ∈ Icc (0 : ℝ) 1, q s y ∈ P.domain)
    (htime : ∀ y ∈ E, ∀ s ∈ Icc (0 : ℝ) 1,
      0 < deriv (fun t => q t y) s 0)
    (htimelike : ∀ y ∈ E, ∀ s ∈ Icc (0 : ℝ) 1,
      0 < quadratic (patchDown P (q s y)) (deriv (fun t => q t y) s))
    (hgeo : ∀ y ∈ E, ∀ s ∈ Icc (0 : ℝ) 1,
      covAcceleration (patchDown P) (patchUp P) (fun t => q t y) s = 0) :
    (∀ k : V3, k ≠ 0 →
      dot3 k (rayVelocity c (P.index z) (P.flow z) k) -
        rayHamiltonian c (P.index z) (P.flow z) k = 0) ∧
    (∀ v : V3, 0 < quadratic (patchDown P z) ![c, v 0, v 1, v 2] →
      massiveLagrangian c (P.index z) m (P.flow z) v =
        -m * c * Real.sqrt (quadratic (patchDown P z) ![c, v 0, v 1, v 2])) ∧
    DifferentiableAt ℝ (endpointAction P m q) z ∧
    (∀ i : Fin 4, -cartesianPartial (endpointAction P m q) z i =
      massiveCovector c m (patchDown P z) (deriv (fun s => q s z) 1) i) ∧
    quadratic (patchUp P z) (QAlgorithms.Papers.Independent.Renew46.P42.gradient (endpointAction P m q) z) = m ^ 2 * c ^ 2 := by
  have hzP : z ∈ P.domain := hEP hz
  have hG : GeoD (patchDown P) (patchUp P) P.domain :=
    { isOpen := P.isOpen
      smooth := patchDown_contDiffOn hc P
      symm := patchDown_symm P
      inv := fun x hx a b => patchDown_mul_patchUp hc P x hx a b }
  have hF : FamD (patchDown P) (patchUp P) P.domain q J E :=
    { hJ := hJ, hE := hE, h01 := h01, hq := hq, himage := himage, htime := htimelike,
      hgeo := hgeo }
  obtain ⟨hA, hA2⟩ := variation_main hG hF hend hz (-m * c)
  have hAeq : endpointAction P m q = fun y => (-m * c) * ∫ s in (0 : ℝ)..1,
      Real.sqrt (quadratic (patchDown P (q s y)) (deriv (fun t => q t y) s)) := rfl
  rw [hAeq] at *
  have hQz : 0 < quadratic (patchDown P z) (deriv (fun t => q t z) 1) := by
    have := htimelike z hz 1 (by simp)
    rwa [(hend z hz).2] at this
  have hpart : ∀ i : Fin 4, -cartesianPartial (fun y => (-m * c) * ∫ s in (0 : ℝ)..1,
      Real.sqrt (quadratic (patchDown P (q s y)) (deriv (fun t => q t y) s))) z i =
      massiveCovector c m (patchDown P z) (deriv (fun s => q s z) 1) i := by
    intro i
    rw [cartesianPartial_eq_of_hasFDerivAt hA i, ContinuousLinearMap.smul_apply, hA2 i]
    unfold massiveCovector apply4
    simp only [Pi.smul_apply, smul_eq_mul]
    have hsqpos : 0 < Real.sqrt (quadratic (patchDown P z) (deriv (fun s => q s z) 1)) :=
      Real.sqrt_pos.mpr hQz
    have hs : ∑ a, patchDown P z a i * deriv (fun t => q t z) 1 a =
        ∑ j, patchDown P z i j * deriv (fun s => q s z) 1 j :=
      Finset.sum_congr rfl (fun a _ => by rw [patchDown_symm P z a i])
    rw [hs]
    field_simp
  refine ⟨?_, ?_, hA.differentiableAt, hpart, ?_⟩
  · intro k hk
    have hz' := hzP
    exact euler_ray c (P.index z) (P.flow z) k hc (P.indexBound z hzP) (P.flowBound z hzP) hk
  · intro v _
    exact massiveLagrangian_eq c (P.index z) m (P.flow z) v
  · have hgrad : QAlgorithms.Papers.Independent.Renew46.P42.gradient (fun y => (-m * c) * ∫ s in (0 : ℝ)..1,
        Real.sqrt (quadratic (patchDown P (q s y)) (deriv (fun t => q t y) s))) z =
        fun i => (-(m * c / Real.sqrt (quadratic (patchDown P z) (deriv (fun s => q s z) 1)))) *
          apply4 (patchDown P z) (deriv (fun s => q s z) 1) i := by
      funext i
      have := hpart i
      unfold QAlgorithms.Papers.Independent.Renew46.P42.gradient
      unfold massiveCovector at this
      simp only [Pi.smul_apply, smul_eq_mul] at this
      linarith
    rw [hgrad, quad_up_massive hc P z hzP]
    have hsq : Real.sqrt (quadratic (patchDown P z) (deriv (fun s => q s z) 1)) ^ 2 =
        quadratic (patchDown P z) (deriv (fun s => q s z) 1) := Real.sq_sqrt hQz.le
    have hne : quadratic (patchDown P z) (deriv (fun s => q s z) 1) ≠ 0 := hQz.ne'
    rw [neg_sq, div_pow, hsq]
    field_simp

