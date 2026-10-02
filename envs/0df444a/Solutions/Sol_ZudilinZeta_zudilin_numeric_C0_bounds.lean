-- Prove2me | solution 1 for ZudilinZeta.zudilin_numeric_C0_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T17:12:14.642084+00:00
-- url     : https://prove2.me/submissions/47e23091-8ba8-460e-b4f6-69bf65cb2166

import Definitions.Def_ZudilinZetaAsymp
import Definitions.Def_ZudilinZetaParams13

set_option autoImplicit false

-- Component: Params13SaddlePolynomial
section
namespace ZudilinZeta

def saddleQ13 (z : ℂ) : ℂ :=
  156*z^7-3872772*z^6+24237617292*z^5+11108559262764*z^4-
    287944618363648812*z^3-265165318728339296652*z^2-
    51416459087006412317436*z-1758025644874743176035740

lemma charPoly_params13_reduction (τ : ℂ) :
    65536*charPoly params13 τ = (2*τ-91)*saddleQ13 ((2*τ-91)^2) := by
  norm_num [charPoly, params13, eta13, Finset.prod_Icc_succ_top, saddleQ13]
  ring

lemma charPoly_params13_reflection (τ : ℂ) :
    charPoly params13 (91-τ) = -charPoly params13 τ := by
  apply mul_left_cancel₀ (a := (65536 : ℂ)) (by norm_num)
  rw [charPoly_params13_reduction, mul_neg, charPoly_params13_reduction]
  rw [show 2*((91 : ℂ)-τ)-91= -(2*τ-91) by ring, neg_sq]
  ring

end ZudilinZeta
end

-- Component: Params13RealRoots
section
open Polynomial

namespace ZudilinZeta

noncomputable def saddleP13 : ℝ[X] :=
  X^7 - C (3872772/156) * X^6 + C (24237617292/156) * X^5 +
    C (11108559262764/156) * X^4 - C (287944618363648812/156) * X^3 -
    C (265165318728339296652/156) * X^2 - C (51416459087006412317436/156) * X -
    C (1758025644874743176035740/156)

lemma saddleP13_natDegree : saddleP13.natDegree = 7 := by
  unfold saddleP13
  compute_degree!

lemma saddleP13_monic : saddleP13.Monic := by
  unfold saddleP13
  monicity!

lemma saddleP13_complex (z : ℂ) : 156 * aeval z saddleP13 = saddleQ13 z := by
  simp [saddleP13, saddleQ13]
  ring

noncomputable def saddleRootLo (i : Fin 5) : ℝ :=
  ![-249790860432482171939476, -68538486020573165705126,
    -21108648548036042162859, -4348103402618084547975,
    1425404304483852874150593] i / 100000000000000000000

noncomputable def saddleRootHi (i : Fin 5) : ℝ :=
  ![-249790860432482171939475, -68538486020573165705125,
    -21108648548036042162858, -4348103402618084547974,
    1425404304483852874150594] i / 100000000000000000000

lemma saddleRoot_intervals (i : Fin 5) : saddleRootLo i < saddleRootHi i := by
  fin_cases i <;> norm_num [saddleRootLo, saddleRootHi]

lemma saddleRoot_intervals_disjoint (i j : Fin 5) (hij : i < j) :
    saddleRootHi i < saddleRootLo j := by
  fin_cases i <;> fin_cases j <;>
    (solve | norm_num at hij | norm_num [saddleRootLo, saddleRootHi])

lemma saddleP13_endpoint_signs (i : Fin 5) :
    (saddleP13.eval (saddleRootLo i) < 0 ∧ 0 < saddleP13.eval (saddleRootHi i)) ∨
    (saddleP13.eval (saddleRootHi i) < 0 ∧ 0 < saddleP13.eval (saddleRootLo i)) := by
  fin_cases i <;> norm_num [saddleP13, saddleRootLo, saddleRootHi]

lemma saddleP13_real_roots : ∃ r : Fin 5 → ℝ,
    StrictMono r ∧ (∀ i, r i ∈ Set.Icc (saddleRootLo i) (saddleRootHi i)) ∧
    ∀ i, saddleP13.eval (r i) = 0 := by
  have h (i : Fin 5) : ∃ x ∈ Set.Icc (saddleRootLo i) (saddleRootHi i),
      saddleP13.eval x = 0 := by
    rcases saddleP13_endpoint_signs i with h | h
    · exact intermediate_value_Icc (saddleRoot_intervals i).le
        saddleP13.continuous.continuousOn ⟨h.1.le, h.2.le⟩
    · exact intermediate_value_Icc' (saddleRoot_intervals i).le
        saddleP13.continuous.continuousOn ⟨h.1.le, h.2.le⟩
  choose r hr he using h
  refine ⟨r, ?_, hr, he⟩
  intro i j hij
  exact (hr i).2.trans_lt ((saddleRoot_intervals_disjoint i j hij).trans_le (hr j).1)

lemma saddleP13_factor (r : Fin 5 → ℝ) (hr : Function.Injective r)
    (hz : ∀ i, saddleP13.eval (r i) = 0) :
    ∃ b c : ℝ,
      saddleP13 = (∏ i, (X - C (r i))) * (X^2 + C b * X + C c) ∧
      b = (∑ i, r i) - 3872772/156 ∧
      (∏ i, r i) * c = 1758025644874743176035740/156 := by
  classical
  let p : ℝ[X] := ∏ i, (X - C (r i))
  have hp : p.Monic := monic_prod_X_sub_C _ _
  have hpd : p.natDegree = 5 := by
    simp [p, natDegree_finsetProd_X_sub_C_eq_card]
  have hdvd : p ∣ saddleP13 := Fintype.prod_dvd_of_coprime
    (pairwise_coprime_X_sub_C hr) (fun i => (dvd_iff_isRoot).mpr (hz i))
  obtain ⟨g, hg⟩ := hdvd
  have hgm : g.Monic := hp.of_mul_monic_left (hg ▸ saddleP13_monic)
  have hgd : g.natDegree = 2 := by
    have hh := hp.natDegree_mul hgm
    rw [← hg, saddleP13_natDegree, hpd] at hh
    omega
  have hgform : g = X^2 + C (g.coeff 1) * X + C (g.coeff 0) := by
    have hh := g.as_sum_range_C_mul_X_pow
    have hc2 : g.coeff 2 = 1 := hgd ▸ hgm.coeff_natDegree
    rw [hgd] at hh
    norm_num [Finset.sum_range_succ, hc2] at hh
    exact hh.trans (by ring)
  refine ⟨g.coeff 1, g.coeff 0, hg.trans (congrArg (p * ·) hgform), ?_, ?_⟩
  · have hh := hp.nextCoeff_mul hgm
    rw [← hg, nextCoeff_of_natDegree_pos (by rw [saddleP13_natDegree]; norm_num),
      saddleP13_natDegree, nextCoeff_of_natDegree_pos (p := g) (by rw [hgd]; norm_num), hgd,
      show p.nextCoeff = -∑ i, r i from prod_X_sub_C_nextCoeff r] at hh
    norm_num [saddleP13] at hh
    linarith
  · have hh := congrArg (fun f : ℝ[X] => f.coeff 0) hg
    norm_num [saddleP13, p, mul_coeff_zero, coeff_zero_prod, Fin.prod_univ_succ] at hh ⊢
    nlinarith only [hh]

end ZudilinZeta
end

-- Component: Params13QuadraticBounds
section
open Polynomial

namespace ZudilinZeta

private lemma mul_bounds {x y a b c d : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    a*c ≤ x*y ∧ x*y ≤ b*d :=
  ⟨mul_le_mul hx.1 hy.1 hc (ha.trans hx.1),
    mul_le_mul hx.2 hy.2 (hc.trans hy.1) (ha.trans (hx.1.trans hx.2))⟩

lemma saddleP13_quadratic_bounds (r : Fin 5 → ℝ) (b c : ℝ)
    (hr : ∀ i, r i ∈ Set.Icc (saddleRootLo i) (saddleRootHi i))
    (hb : b = (∑ i, r i) - 3872772/156)
    (hc : (∏ i, r i) * c = 1758025644874743176035740/156) :
    (-14009279477660105/1000000000000 ≤ b ∧ b ≤ -14009279477660104/1000000000000) ∧
    (50314272573632/1000000 ≤ c ∧ c ≤ 50314272573633/1000000) := by
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  have h3 := hr 3
  have h4 := hr 4
  norm_num [saddleRootLo, saddleRootHi, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four] at h0 h1 h2 h3 h4
  constructor
  · simp [Fin.sum_univ_succ] at hb
    constructor <;> linarith only [hb, h0.1, h0.2, h1.1, h1.2,
      h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
  · have p0 : 249790860432482171939475/100000000000000000000 ≤ -r 0 ∧
        -r 0 ≤ 249790860432482171939476/100000000000000000000 := by
      constructor <;> linarith only [h0.1, h0.2]
    have p1 : 68538486020573165705125/100000000000000000000 ≤ -r 1 ∧
        -r 1 ≤ 68538486020573165705126/100000000000000000000 := by
      constructor <;> linarith only [h1.1, h1.2]
    have p2 : 21108648548036042162858/100000000000000000000 ≤ -r 2 ∧
        -r 2 ≤ 21108648548036042162859/100000000000000000000 := by
      constructor <;> linarith only [h2.1, h2.2]
    have p3 : 4348103402618084547974/100000000000000000000 ≤ -r 3 ∧
        -r 3 ≤ 4348103402618084547975/100000000000000000000 := by
      constructor <;> linarith only [h3.1, h3.2]
    have pp := mul_bounds (by norm_num) (by norm_num) p0 p1
    have pp := mul_bounds (by norm_num) (by norm_num) pp p2
    have pp := mul_bounds (by norm_num) (by norm_num) pp p3
    have pp := mul_bounds (by norm_num) (by norm_num) pp h4
    have he : -r 0 * -r 1 * -r 2 * -r 3 * r 4 = ∏ i, r i := by
      simp [Fin.prod_univ_succ]
      ring
    rw [he] at pp
    have hp : 223980087220006264014/1000000 ≤ ∏ i, r i ∧
        (∏ i, r i) ≤ 223980087220006264015/1000000 := by
      constructor <;> norm_num at pp ⊢ <;> linarith only [pp.1, pp.2]
    have hpos : 0 < c := by
      by_contra hh
      have := mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ ∏ i, r i by linarith only [hp.1]) (le_of_not_gt hh)
      linarith only [this, hc]
    constructor
    · nlinarith only [hc, mul_le_mul_of_nonneg_right hp.2 hpos.le]
    · nlinarith only [hc, mul_le_mul_of_nonneg_right hp.1 hpos.le]

end ZudilinZeta
end

-- Component: Params13SaddleGeometry
section
open Polynomial

namespace ZudilinZeta

lemma quadratic_nonreal_coordinates (b c : ℝ) (hd : b^2 < 4*c) (z : ℂ)
    (hz : z^2 + (b : ℂ)*z + (c : ℂ) = 0) :
    z.re = -b/2 ∧ z.re^2 + z.im^2 = c := by
  have hRe := congrArg Complex.re hz
  have hIm := congrArg Complex.im hz
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hRe hIm
  have hne : z.im ≠ 0 := by
    intro he
    rw [he] at hRe
    nlinarith only [hd, hRe, sq_nonneg (2*z.re+b)]
  have hh : (2*z.re+b)*z.im = 0 := by nlinarith only [hIm]
  have hh := (mul_eq_zero.mp hh).resolve_right hne
  constructor
  · linarith only [hh]
  · have hb : b = -2*z.re := by linarith only [hh]
    rw [hb] at hRe
    nlinarith only [hRe]

lemma saddleP13_quartic_coordinates (b c : ℝ)
    (hb : -14009279477660105/1000000000000 ≤ b ∧ b ≤ -14009279477660104/1000000000000)
    (hc : 50314272573632/1000000 ≤ c ∧ c ≤ 50314272573633/1000000) :
    ∃ u v : ℝ, 0 < u ∧ 0 < v ∧
      u^2-v^2 = -b/2 ∧ (u^2+v^2)^2 = c ∧
      (87479005418345/1000000000000 ≤ (u+91)/2 ∧
        (u+91)/2 ≤ 87479005418346/1000000000000) ∧
      (3328206905525/1000000000000 ≤ v/2 ∧
        v/2 ≤ 3328206905527/1000000000000) := by
  let s := Real.sqrt c
  have hs0 : 0 ≤ s := Real.sqrt_nonneg c
  have hs2 : s^2 = c := Real.sq_sqrt (by linarith only [hc.1])
  have hs : 709325542847795/100000000000 ≤ s ∧
      s ≤ 709325542847803/100000000000 := by
    constructor
    · nlinarith only [hs0, hs2, hc.1]
    · nlinarith only [hs0, hs2, hc.2]
  let u := Real.sqrt ((s-b/2)/2)
  let v := Real.sqrt ((s+b/2)/2)
  have hu0 : 0 < u := Real.sqrt_pos.mpr (by linarith only [hs.1, hb.2])
  have hv0 : 0 < v := Real.sqrt_pos.mpr (by linarith only [hs.1, hb.1])
  have hu2 : u^2 = (s-b/2)/2 := Real.sq_sqrt (by linarith only [hs.1, hb.2])
  have hv2 : v^2 = (s+b/2)/2 := Real.sq_sqrt (by linarith only [hs.1, hb.1])
  refine ⟨u, v, hu0, hv0, ?_, ?_, ?_, ?_⟩
  · linarith only [hu2, hv2]
  · rw [show u^2+v^2=s by linarith only [hu2, hv2], hs2]
  · constructor
    · nlinarith only [hu0, hu2, hs.1, hb.2]
    · nlinarith only [hu0, hu2, hs.2, hb.1]
  · constructor
    · nlinarith only [hv0, hv2, hs.1, hb.1]
    · nlinarith only [hv0, hv2, hs.2, hb.2]

lemma quartic_root_of_coordinates (b c u v : ℝ)
    (huv : u^2-v^2 = -b/2) (hc : (u^2+v^2)^2=c) :
    (((u : ℂ)+(v : ℂ)*Complex.I)^2)^2 +
      (b : ℂ)*((u : ℂ)+(v : ℂ)*Complex.I)^2 + (c : ℂ) = 0 := by
  have hb : b = -2*(u^2-v^2) := by linarith only [huv]
  rw [hb, ← hc]
  push_cast
  ring_nf
  norm_num [Complex.I_sq, pow_succ]
  ring

lemma quartic_root_re_le (b c u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (huv : u^2-v^2 = -b/2) (hc : (u^2+v^2)^2=c)
    (z : ℂ) (hz : (z^2)^2 + (b : ℂ)*z^2 + (c : ℂ)=0) : z.re ≤ u := by
  have hd : b^2 < 4*c := by
    have hh := mul_pos (sq_pos_of_pos hu) (sq_pos_of_pos hv)
    rw [show b = -2*(u^2-v^2) by linarith only [huv], ← hc]
    nlinarith only [hh]
  obtain ⟨hr, hn⟩ := quadratic_nonreal_coordinates b c hd (z^2) hz
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hr hn
  have hn' : (z.re^2+z.im^2)^2=(u^2+v^2)^2 := by nlinarith only [hn, hc]
  have he : z.re^2+z.im^2=u^2+v^2 :=
    (sq_eq_sq₀ (by positivity) (by positivity)).mp hn'
  nlinarith only [hr, huv, he, hu]

lemma saddleP13_factor_complex (r : Fin 5 → ℝ) (b c : ℝ)
    (hf : saddleP13 = (∏ i, (X-C (r i))) * (X^2+C b*X+C c)) (z : ℂ) :
    saddleQ13 z = 156*(∏ i, (z-(r i : ℂ)))*(z^2+(b : ℂ)*z+(c : ℂ)) := by
  rw [← saddleP13_complex, hf]
  simp [map_prod]
  ring

lemma saddle_root_params13_geometry :
    ∃ τ₀ : ℂ, charPoly params13 τ₀=0 ∧ 0<τ₀.im ∧
      (∀ τ : ℂ, charPoly params13 τ=0 → 0<τ.im → τ.re≤τ₀.re) ∧
      (87479005418345/1000000000000 ≤ τ₀.re ∧
        τ₀.re ≤ 87479005418346/1000000000000) ∧
      (3328206905525/1000000000000 ≤ τ₀.im ∧
        τ₀.im ≤ 3328206905527/1000000000000) := by
  obtain ⟨r, hmono, hbounds, hroots⟩ := saddleP13_real_roots
  obtain ⟨b, c, hfactor, hb, hc⟩ := saddleP13_factor r hmono.injective hroots
  obtain ⟨hb', hc'⟩ := saddleP13_quadratic_bounds r b c hbounds hb hc
  obtain ⟨u, v, hu, hv, huv, hc2, hure, hvim⟩ := saddleP13_quartic_coordinates b c hb' hc'
  let w : ℂ := (u : ℂ)+(v : ℂ)*Complex.I
  let τ₀ : ℂ := (w+91)/2
  have hwre : w.re=u := by simp [w]
  have hwim : w.im=v := by simp [w]
  have hτre : τ₀.re=(u+91)/2 := by simp [τ₀, hwre]
  have hτim : τ₀.im=v/2 := by simp [τ₀, hwim]
  have hw : 2*τ₀-91=w := by dsimp only [τ₀]; ring
  have hwroot : saddleQ13 (w^2)=0 := by
    rw [saddleP13_factor_complex r b c hfactor,
      quartic_root_of_coordinates b c u v huv hc2, mul_zero]
  refine ⟨τ₀, ?_, by rw [hτim]; positivity, ?_, hτre.symm ▸ hure, hτim.symm ▸ hvim⟩
  · have hh := charPoly_params13_reduction τ₀
    rw [hw, hwroot, mul_zero] at hh
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
  · intro τ hτ hτi
    let z : ℂ := 2*τ-91
    have hzre : z.re=2*τ.re-91 := by simp [z]
    have hzim : z.im=2*τ.im := by simp [z]
    have hzpos : 0<z.im := by rw [hzim]; positivity
    have hz0 : z≠0 := by
      intro he
      rw [he, Complex.zero_im] at hzpos
      exact lt_irrefl _ hzpos
    have hq : saddleQ13 (z^2)=0 := by
      have hh := charPoly_params13_reduction τ
      rw [hτ, mul_zero] at hh
      exact (mul_eq_zero.mp hh.symm).resolve_left hz0
    rw [saddleP13_factor_complex r b c hfactor] at hq
    rcases mul_eq_zero.mp hq with hq | hq
    · have hp : (∏ i, (z^2-(r i : ℂ)))=0 :=
        (mul_eq_zero.mp hq).resolve_left (by norm_num)
      obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hp
      have hi := congrArg Complex.im (sub_eq_zero.mp hi)
      simp [pow_two, Complex.mul_im] at hi
      have hzre0 : z.re=0 := by nlinarith only [hi, hzpos]
      rw [hτre]
      linarith only [hzre, hzre0, hu]
    · have hh := quartic_root_re_le b c u v hu hv huv hc2 z hq
      rw [hτre]
      linarith only [hzre, hh]

end ZudilinZeta
end

-- Component: Params13SaddleUniqueness
section
open Polynomial

namespace ZudilinZeta

lemma saddle_params13_right_root_unique (τ σ : ℂ)
    (hτ : charPoly params13 τ=0) (hσ : charPoly params13 σ=0)
    (hτi : 0<τ.im) (hσi : 0<σ.im) (hτr : 91/2<τ.re) (hre : τ.re=σ.re) : τ=σ := by
  obtain ⟨r, hmono, hbounds, hroots⟩ := saddleP13_real_roots
  obtain ⟨b, c, hfactor, hb, hc⟩ := saddleP13_factor r hmono.injective hroots
  obtain ⟨hb', hc'⟩ := saddleP13_quadratic_bounds r b c hbounds hb hc
  have hd : b^2<4*c := by
    have hh := mul_nonneg (show 0≤b+14010 by linarith only [hb'.1])
      (show 0≤14010-b by linarith only [hb'.2])
    nlinarith only [hh, hc'.1]
  have hquad (z : ℂ) (hz : charPoly params13 z=0) (hzi : 0<z.im)
      (hzr : 91/2<z.re) : ((2*z-91)^2)^2+(b : ℂ)*(2*z-91)^2+(c : ℂ)=0 := by
    have hi : 0<(2*z-91).im := by norm_num; linarith only [hzi]
    have hr : 0<(2*z-91).re := by norm_num; linarith only [hzr]
    have hn : 2*z-91≠0 := by
      intro he
      rw [he, Complex.zero_im] at hi
      exact lt_irrefl _ hi
    have hh := charPoly_params13_reduction z
    rw [hz, mul_zero] at hh
    have hq := (mul_eq_zero.mp hh.symm).resolve_left hn
    rw [saddleP13_factor_complex r b c hfactor] at hq
    rcases mul_eq_zero.mp hq with hq | hq
    · have hp : (∏ i, ((2*z-91)^2-(r i : ℂ)))=0 :=
        (mul_eq_zero.mp hq).resolve_left (by norm_num)
      obtain ⟨i, _, he⟩ := Finset.prod_eq_zero_iff.mp hp
      have he := congrArg Complex.im (sub_eq_zero.mp he)
      simp only [pow_two, Complex.mul_im, Complex.ofReal_im] at he
      nlinarith only [he, mul_pos hr hi]
    · exact hq
  have ha := (quadratic_nonreal_coordinates b c hd ((2*τ-91)^2)
    (hquad τ hτ hτi hτr)).1
  have hs := (quadratic_nonreal_coordinates b c hd ((2*σ-91)^2)
    (hquad σ hσ hσi (by simpa only [← hre] using hτr))).1
  norm_num [pow_two, Complex.mul_re, Complex.mul_im] at ha hs
  rw [← hre] at hs
  have himsq : τ.im^2=σ.im^2 := by nlinarith only [ha, hs]
  exact Complex.ext hre ((sq_eq_sq₀ hτi.le hσi.le).mp himsq)

lemma saddle_params13_maximal_root_box (τ : ℂ) (hτ : charPoly params13 τ=0)
    (hτi : 0<τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ=0 → 0<σ.im → σ.re≤τ.re) :
    (87479005418345/1000000000000 ≤ τ.re ∧
      τ.re ≤ 87479005418346/1000000000000) ∧
    (3328206905525/1000000000000 ≤ τ.im ∧
      τ.im ≤ 3328206905527/1000000000000) := by
  obtain ⟨σ, hσ, hσi, hσmax, hx, hy⟩ := saddle_root_params13_geometry
  have hre : τ.re=σ.re := le_antisymm (hσmax τ hτ hτi) (hmax σ hσ hσi)
  have he := saddle_params13_right_root_unique τ σ hτ hσ hτi hσi
    (by rw [hre]; linarith only [hx.1]) hre
  simpa only [he] using And.intro hx hy

end ZudilinZeta
end

-- Component: LogRationalBounds
section
namespace ZudilinZeta

noncomputable def logSeries (n : ℕ) (z : ℝ) : ℝ :=
  2 * ∑ i ∈ Finset.range n, z^(2*i+1)/(2*i+1)

lemma logSeries_bounds (n : ℕ) (z : ℝ) (hz0 : 0≤z) (hz1 : z<1) :
    logSeries n z ≤ Real.log ((1+z)/(1-z)) ∧
    Real.log ((1+z)/(1-z)) ≤ logSeries n z+2*z^(2*n+1)/(1-z^2) := by
  have hl := Real.sum_range_le_log_div hz0 hz1 n
  have hu := Real.log_div_le_sum_range_add hz0 hz1 n
  dsimp only [logSeries]
  constructor
  · linarith only [hl]
  · rw [mul_div_assoc]
    linarith only [hu]

lemma log_two_precise_bounds :
    693147180559945/1000000000000000 ≤ Real.log 2 ∧
    Real.log 2 ≤ 693147180559946/1000000000000000 := by
  have h := logSeries_bounds 16 (1/3) (by norm_num) (by norm_num)
  norm_num [logSeries, Finset.sum_range_succ] at h
  constructor <;> linarith only [h.1, h.2]

lemma scaled_log_enclosure (x : ℝ) (k n : ℕ) (l u a b : ℝ) (hx : 0<x)
    (hl0 : 0≤l) (hl1 : l<1) (hu0 : 0≤u) (hu1 : u<1)
    (hxl : (1+l)*2^k ≤ x*(1-l)) (hxu : x*(1-u) ≤ (1+u)*2^k)
    (ha : a ≤ (k : ℝ)*(693147180559945/1000000000000000)+logSeries n l)
    (hb : (k : ℝ)*(693147180559946/1000000000000000)+
      logSeries n u+2*u^(2*n+1)/(1-u^2) ≤ b) :
    a ≤ Real.log x ∧ Real.log x ≤ b := by
  have hl := (logSeries_bounds n l hl0 hl1).1
  have hu := (logSeries_bounds n u hu0 hu1).2
  have hp : 0<(2 : ℝ)^k := by positivity
  have hle : (1+l)/(1-l) ≤ x/2^k :=
    (div_le_div_iff₀ (by linarith only [hl1]) hp).mpr hxl
  have hue : x/2^k ≤ (1+u)/(1-u) :=
    (div_le_div_iff₀ hp (by linarith only [hu1])).mpr hxu
  have hlogl := Real.log_le_log (by positivity : 0<(1+l)/(1-l)) hle
  have hlogu := Real.log_le_log (div_pos hx hp) hue
  rw [Real.log_div hx.ne' hp.ne', Real.log_pow] at hlogl hlogu
  have hkl := mul_le_mul_of_nonneg_left log_two_precise_bounds.1 (Nat.cast_nonneg k)
  have hku := mul_le_mul_of_nonneg_left log_two_precise_bounds.2 (Nat.cast_nonneg k)
  constructor <;> linarith only [ha, hb, hl, hu, hlogl, hlogu, hkl, hku]

lemma complex_log_re_normSq (z : ℂ) :
    (Complex.log z).re = Real.log (Complex.normSq z)/2 := by
  rw [Complex.log_re, Complex.normSq_eq_norm_sq, Real.log_pow]
  norm_num

lemma squared_distance_bounds (x y a lx ux ly uy : ℝ)
    (hx : lx≤x ∧ x≤ux) (hy : ly≤y ∧ y≤uy)
    (ha : a≤lx) (hl : 0≤ly) :
    (lx-a)^2+ly^2 ≤ (x-a)^2+y^2 ∧ (x-a)^2+y^2 ≤ (ux-a)^2+uy^2 := by
  have hx0 : 0≤lx-a := sub_nonneg.mpr ha
  constructor
  · exact add_le_add (pow_le_pow_left₀ hx0 (sub_le_sub_right hx.1 a) 2)
      (pow_le_pow_left₀ hl hy.1 2)
  · exact add_le_add (pow_le_pow_left₀ (hx0.trans (sub_le_sub_right hx.1 a))
        (sub_le_sub_right hx.2 a) 2)
      (pow_le_pow_left₀ (hl.trans hy.1) hy.2 2)

end ZudilinZeta
end

-- Component: Params13C0Formula
section
namespace ZudilinZeta

lemma C0_params13_log_formula (τ : ℂ) :
    2*C0 params13 τ =
      -273*Real.log ((τ.re-91)^2+τ.im^2)
      -81*Real.log ((τ.re-27)^2+τ.im^2)
      +192*Real.log ((τ.re-64)^2+τ.im^2)
      + (∑ j ∈ Finset.Icc (29 : ℕ) 38,
          ((91-j)*Real.log ((τ.re-(91-j))^2+τ.im^2)-
            j*Real.log ((τ.re-j)^2+τ.im^2)))
      +324*Real.log 27
      -2*∑ j ∈ Finset.Icc (29 : ℕ) 38, (91-2*j)*Real.log (91-2*j) := by
  have hn (z : ℂ) : Real.log ‖z‖ = Real.log (Complex.normSq z)/2 := by
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]
    norm_num
  norm_num [C0, f0, params13, eta13, Finset.sum_Icc_succ_top, Complex.mul_re,
    Complex.log_re]
  simp_rw [hn]
  norm_num [Complex.normSq_apply, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im]
  ring_nf

end ZudilinZeta
end

-- Component: Params13C0Bounds
section
namespace ZudilinZeta

-- All generated numerical claims below are exact rational inequalities.
private lemma c0_log_n27 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (82076163844039/10000000000000) ≤ Real.log ((τ.re-27)^2+τ.im^2) ∧ Real.log ((τ.re-27)^2+τ.im^2) ≤ (2051904096101/250000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 27
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 11 16 (28351363121773/100000000000000) (70878407804437/250000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n29 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (20351423635637/2500000000000) ≤ Real.log ((τ.re-29)^2+τ.im^2) ∧ Real.log ((τ.re-29)^2+τ.im^2) ≤ (81405694542549/10000000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 29
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 11 16 (403841164169/1600000000000) (63100181901411/250000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n30 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (81061866654999/10000000000000) ≤ Real.log ((τ.re-30)^2+τ.im^2) ∧ Real.log ((τ.re-30)^2+τ.im^2) ≤ (16212373331/2000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 30
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 11 16 (23623598204211/100000000000000) (236235982042129/1000000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n31 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (20178011215541/2500000000000) ≤ Real.log ((τ.re-31)^2+τ.im^2) ∧ Real.log ((τ.re-31)^2+τ.im^2) ≤ (16142408972433/2000000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 31
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 11 16 (54913549988571/250000000000000) (1716048437143/7812500000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n32 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (40178008614177/5000000000000) ≤ Real.log ((τ.re-32)^2+τ.im^2) ∧ Real.log ((τ.re-32)^2+τ.im^2) ≤ (20089004307089/2500000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 32
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 11 16 (12665437155243/62500000000000) (50661748620977/250000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n33 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (4999597526111/625000000000) ≤ Real.log ((τ.re-33)^2+τ.im^2) ∧ Real.log ((τ.re-33)^2+τ.im^2) ≤ (39996780208889/5000000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 33
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 11 16 (92603120241621/500000000000000) (185206240483263/1000000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n34 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (79624438865297/10000000000000) ≤ Real.log ((τ.re-34)^2+τ.im^2) ∧ Real.log ((τ.re-34)^2+τ.im^2) ≤ (39812219432649/5000000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 34
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 11 16 (20915517166633/125000000000000) (83662068666543/500000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n35 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (3962420193537/500000000000) ≤ Real.log ((τ.re-35)^2+τ.im^2) ∧ Real.log ((τ.re-35)^2+τ.im^2) ≤ (39624201935371/5000000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 35
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 11 16 (74496639213217/500000000000000) (18624159803307/125000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n36 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (39432596304071/5000000000000) ≤ Real.log ((τ.re-36)^2+τ.im^2) ∧ Real.log ((τ.re-36)^2+τ.im^2) ≤ (4929074538009/625000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 36
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 11 16 (4068960243399/31250000000000) (13020672778879/100000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n37 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (19618631760059/2500000000000) ≤ Real.log ((τ.re-37)^2+τ.im^2) ∧ Real.log ((τ.re-37)^2+τ.im^2) ≤ (39237263520119/5000000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 37
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 11 16 (13869763038227/125000000000000) (110958104305839/1000000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n38 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (39038056363571/5000000000000) ≤ Real.log ((τ.re-38)^2+τ.im^2) ∧ Real.log ((τ.re-38)^2+τ.im^2) ≤ (9759514090893/1250000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 38
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 11 16 (9124167402679/100000000000000) (45620837013407/500000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n53 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (35449879052717/5000000000000) ≤ Real.log ((τ.re-53)^2+τ.im^2) ∧ Real.log ((τ.re-53)^2+τ.im^2) ≤ (14179951621087/2000000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 53
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 10 16 (79086494171643/1000000000000000) (39543247085839/500000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n54 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (70316712607369/10000000000000) ≤ Real.log ((τ.re-54)^2+τ.im^2) ∧ Real.log ((τ.re-54)^2+τ.im^2) ≤ (70316712607371/10000000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 54
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 10 16 (50057853126703/1000000000000000) (50057853126739/1000000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n55 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (69716336643131/10000000000000) ≤ Real.log ((τ.re-55)^2+τ.im^2) ∧ Real.log ((τ.re-55)^2+τ.im^2) ≤ (69716336643133/10000000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 55
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 10 16 (20078230622591/1000000000000000) (5019557655657/250000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n56 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (13819516031/2000000000) ≤ Real.log ((τ.re-56)^2+τ.im^2) ∧ Real.log ((τ.re-56)^2+τ.im^2) ≤ (34548790077501/5000000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 56
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 9 16 (161824044968009/500000000000000) (323648089936053/1000000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n57 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (68459295894511/10000000000000) ≤ Real.log ((τ.re-57)^2+τ.im^2) ∧ Real.log ((τ.re-57)^2+τ.im^2) ≤ (68459295894513/10000000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 57
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 9 16 (294788537391807/1000000000000000) (73697134347961/250000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n58 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (67800227224593/10000000000000) ≤ Real.log ((τ.re-58)^2+τ.im^2) ∧ Real.log ((τ.re-58)^2+τ.im^2) ≤ (13560045444919/2000000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 58
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 9 16 (52882939992741/200000000000000) (8262959373867/31250000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n59 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (16779748495039/2500000000000) ≤ Real.log ((τ.re-59)^2+τ.im^2) ∧ Real.log ((τ.re-59)^2+τ.im^2) ≤ (33559496990079/5000000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 59
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 9 16 (232459014928557/1000000000000000) (116229507464299/500000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n60 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (16603519003079/2500000000000) ≤ Real.log ((τ.re-60)^2+τ.im^2) ∧ Real.log ((τ.re-60)^2+τ.im^2) ≤ (33207038006159/5000000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 60
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 9 16 (49714076194461/250000000000000) (6214259524309/31250000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n61 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (65683793956671/10000000000000) ≤ Real.log ((τ.re-61)^2+τ.im^2) ∧ Real.log ((τ.re-61)^2+τ.im^2) ≤ (65683793956673/10000000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 61
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 9 16 (16354540663911/100000000000000) (40886351659789/250000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n62 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (64926286659523/10000000000000) ≤ Real.log ((τ.re-62)^2+τ.im^2) ∧ Real.log ((τ.re-62)^2+τ.im^2) ≤ (2597051466381/400000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 62
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 9 16 (63235586990753/500000000000000) (25294234796311/200000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n64 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (63321078168647/10000000000000) ≤ Real.log ((τ.re-64)^2+τ.im^2) ∧ Real.log ((τ.re-64)^2+τ.im^2) ≤ (63321078168649/10000000000000) := by
  have hd := squared_distance_bounds τ.re τ.im 64
    (17495801083669/200000000000) (43739502709173/500000000000) (133128276221/40000000000) (3328206905527/1000000000000) hx hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 9 16 (23428628680063/500000000000000) (2342862868009/50000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_n91 (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    (1972443083879/625000000000) ≤ Real.log ((91-τ.re)^2+τ.im^2) ∧ Real.log ((91-τ.re)^2+τ.im^2) ≤ (15779544671037/5000000000000) := by
  have hd := squared_distance_bounds (91-τ.re) τ.im 0
    (1760497290827/500000000000) (704198916331/200000000000) (133128276221/40000000000) (3328206905527/1000000000000)
    ⟨by linarith only [hx.2], by linarith only [hx.1]⟩ hy (by norm_num) (by norm_num)
  norm_num at hd
  refine scaled_log_enclosure _ 4 16 (94673647440523/500000000000000) (37869458976293/200000000000000) _ _
    (by linarith only [hd.1]) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by nlinarith only [hd.1]) (by nlinarith only [hd.2]) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_c15 :
    (13540251005511/5000000000000) ≤ Real.log 15 ∧ Real.log 15 ≤ (27080502011023/10000000000000) := by
  refine scaled_log_enclosure 15 3 16 (76086956521739/250000000000000) (304347826086957/1000000000000000) _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_c17 :
    (14166066720281/5000000000000) ≤ Real.log 17 ∧ Real.log 17 ≤ (28332133440563/10000000000000) := by
  refine scaled_log_enclosure 17 4 16 (3030303030303/100000000000000) (30303030303031/1000000000000000) _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_c19 :
    (1840274361979/625000000000) ≤ Real.log 19 ∧ Real.log 19 ≤ (5888877958333/2000000000000) := by
  refine scaled_log_enclosure 19 4 16 (17142857142857/200000000000000) (42857142857143/500000000000000) _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_c21 :
    (15222612188617/5000000000000) ≤ Real.log 21 ∧ Real.log 21 ≤ (6089044875447/2000000000000) := by
  refine scaled_log_enclosure 21 4 16 (27027027027027/200000000000000) (4222972972973/31250000000000) _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_c23 :
    (31354942159291/10000000000000) ≤ Real.log 23 ∧ Real.log 23 ≤ (7838735539823/2500000000000) := by
  refine scaled_log_enclosure 23 4 16 (179487179487179/1000000000000000) (8974358974359/50000000000000) _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_c25 :
    (32188758248681/10000000000000) ≤ Real.log 25 ∧ Real.log 25 ≤ (32188758248683/10000000000000) := by
  refine scaled_log_enclosure 25 4 16 (219512195121951/1000000000000000) (6859756097561/31250000000000) _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_c27 :
    (32958368660043/10000000000000) ≤ Real.log 27 ∧ Real.log 27 ≤ (8239592165011/2500000000000) := by
  refine scaled_log_enclosure 27 4 16 (63953488372093/250000000000000) (255813953488373/1000000000000000) _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_c29 :
    (4209119787483/1250000000000) ≤ Real.log 29 ∧ Real.log 29 ≤ (6734591659973/2000000000000) := by
  refine scaled_log_enclosure 29 4 16 (36111111111111/125000000000000) (288888888888889/1000000000000000) _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_c31 :
    (34339872044851/10000000000000) ≤ Real.log 31 ∧ Real.log 31 ≤ (8584968011213/2500000000000) := by
  refine scaled_log_enclosure 31 4 16 (79787234042553/250000000000000) (319148936170213/1000000000000000) _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

private lemma c0_log_c33 :
    (4370634451833/1250000000000) ≤ Real.log 33 ∧ Real.log 33 ≤ (6993015122933/2000000000000) := by
  refine scaled_log_enclosure 33 5 16 (3076923076923/200000000000000) (1923076923077/125000000000000) _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ ?_
  · norm_num [logSeries, Finset.sum_range_succ]
  · norm_num [logSeries, Finset.sum_range_succ]

lemma C0_params13_enclosure_of_box (τ : ℂ)
    (hx : (17495801083669/200000000000) ≤ τ.re ∧ τ.re ≤ (43739502709173/500000000000)) (hy : (133128276221/40000000000) ≤ τ.im ∧ τ.im ≤ (3328206905527/1000000000000)) :
    227.58019641 ≤ C0 params13 τ ∧ C0 params13 τ < 227.58019642 := by
  have hn27 := c0_log_n27 τ hx hy
  have hn29 := c0_log_n29 τ hx hy
  have hn30 := c0_log_n30 τ hx hy
  have hn31 := c0_log_n31 τ hx hy
  have hn32 := c0_log_n32 τ hx hy
  have hn33 := c0_log_n33 τ hx hy
  have hn34 := c0_log_n34 τ hx hy
  have hn35 := c0_log_n35 τ hx hy
  have hn36 := c0_log_n36 τ hx hy
  have hn37 := c0_log_n37 τ hx hy
  have hn38 := c0_log_n38 τ hx hy
  have hn53 := c0_log_n53 τ hx hy
  have hn54 := c0_log_n54 τ hx hy
  have hn55 := c0_log_n55 τ hx hy
  have hn56 := c0_log_n56 τ hx hy
  have hn57 := c0_log_n57 τ hx hy
  have hn58 := c0_log_n58 τ hx hy
  have hn59 := c0_log_n59 τ hx hy
  have hn60 := c0_log_n60 τ hx hy
  have hn61 := c0_log_n61 τ hx hy
  have hn62 := c0_log_n62 τ hx hy
  have hn64 := c0_log_n64 τ hx hy
  have hn91 := c0_log_n91 τ hx hy
  have hc15 := c0_log_c15
  have hc17 := c0_log_c17
  have hc19 := c0_log_c19
  have hc21 := c0_log_c21
  have hc23 := c0_log_c23
  have hc25 := c0_log_c25
  have hc27 := c0_log_c27
  have hc29 := c0_log_c29
  have hc31 := c0_log_c31
  have hc33 := c0_log_c33
  have he := C0_params13_log_formula τ
  norm_num [Finset.sum_Icc_succ_top] at he
  ring_nf at he hn27 hn29 hn30 hn31 hn32 hn33 hn34 hn35 hn36 hn37 hn38 hn53 hn54 hn55 hn56 hn57 hn58 hn59 hn60 hn61 hn62 hn64 hn91 hc15 hc17 hc19 hc21 hc23 hc25 hc27 hc29 hc31 hc33
  constructor <;> linarith only [he, hn27.1, hn27.2, hn29.1, hn29.2, hn30.1, hn30.2, hn31.1, hn31.2, hn32.1, hn32.2, hn33.1, hn33.2, hn34.1, hn34.2, hn35.1, hn35.2, hn36.1, hn36.2, hn37.1, hn37.2, hn38.1, hn38.2, hn53.1, hn53.2, hn54.1, hn54.2, hn55.1, hn55.2, hn56.1, hn56.2, hn57.1, hn57.2, hn58.1, hn58.2, hn59.1, hn59.2, hn60.1, hn60.2, hn61.1, hn61.2, hn62.1, hn62.2, hn64.1, hn64.2, hn91.1, hn91.2, hc15.1, hc15.2, hc17.1, hc17.2, hc19.1, hc19.2, hc21.1, hc21.2, hc23.1, hc23.2, hc25.1, hc25.2, hc27.1, hc27.2, hc29.1, hc29.2, hc31.1, hc31.2, hc33.1, hc33.2]

lemma C0_params13_enclosure (τ : ℂ) (hroot : charPoly params13 τ=0)
    (him : 0<τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ=0 → 0<σ.im → σ.re≤τ.re) :
    227.58019641 ≤ C0 params13 τ ∧ C0 params13 τ < 227.58019642 := by
  obtain ⟨hx, hy⟩ := saddle_params13_maximal_root_box τ hroot him hmax
  norm_num at hx hy
  exact C0_params13_enclosure_of_box τ hx hy

end ZudilinZeta
end

open ZudilinZeta

theorem solution (τ : ℂ) (hroot : charPoly params13 τ = 0) (him : 0 < τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ = 0 → 0 < σ.im → σ.re ≤ τ.re) :
    227.58019641 ≤ C0 params13 τ ∧ C0 params13 τ < 227.58019642 := by
  exact C0_params13_enclosure τ hroot him hmax
