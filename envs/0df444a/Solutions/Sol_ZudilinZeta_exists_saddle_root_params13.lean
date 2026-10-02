-- Prove2me | solution 1 for ZudilinZeta.exists_saddle_root_params13
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T16:38:06.236373+00:00
-- url     : https://prove2.me/submissions/54ec65ef-588d-472a-a570-bc037b827491

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

-- Component: SaddleArctanBounds
section
namespace ZudilinZeta

lemma arctan_cubic_lower (x : ℝ) (hx : 0 ≤ x) :
    x-x^3/3 ≤ Real.arctan x := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => Real.arctan t-(t-t^3/3))
      (t^4/(1+t^2)) t := by
    convert (Real.hasDerivAt_arctan t).sub
      ((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 3).div_const 3)) using 1 <;>
      (first | rfl | (simp only [id_eq]; field_simp; ring))
  have hm := monotone_of_hasDerivAt_nonneg hd (fun t => by positivity)
  have hh := hm hx
  norm_num at hh
  linarith only [hh]

lemma arctan_quintic_upper (x : ℝ) (hx : 0 ≤ x) :
    Real.arctan x ≤ x-x^3/3+x^5/5 := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => t-t^3/3+t^5/5-Real.arctan t)
      (t^6/(1+t^2)) t := by
    convert (((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 3).div_const 3)).add
      (((hasDerivAt_id t).pow 5).div_const 5)).sub (Real.hasDerivAt_arctan t) using 1 <;>
      (first | rfl | (simp only [id_eq]; field_simp; ring))
  have hm := monotone_of_hasDerivAt_nonneg hd (fun t => by positivity)
  have hh := hm hx
  norm_num at hh
  linarith only [hh]

lemma arctan_rational_enclosure (x l u a b : ℝ) (hl : 0 ≤ l)
    (hx : l ≤ x ∧ x ≤ u) (ha : a ≤ l-l^3/3) (hb : u-u^3/3+u^5/5 ≤ b) :
    a ≤ Real.arctan x ∧ Real.arctan x ≤ b :=
  ⟨ha.trans ((arctan_cubic_lower l hl).trans (Real.arctan_le_arctan_iff.mpr hx.1)),
    (Real.arctan_le_arctan_iff.mpr hx.2).trans
      ((arctan_quintic_upper u (hl.trans (hx.1.trans hx.2))).trans hb)⟩

lemma arg_eq_arctan_of_re_pos (z : ℂ) (hr : 0 < z.re) :
    z.arg = Real.arctan (z.im/z.re) := by
  have hh := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hr))
  rw [← Complex.tan_arg, Real.arctan_tan hh.1 hh.2]

lemma arctan_complement_quarter (y d : ℝ) (hy : 0 < y) (hyd : y < d) :
    Real.arctan (y/d) = Real.pi/4-Real.arctan ((d-y)/(d+y)) := by
  have hd : 0<d := hy.trans hyd
  have hdy : 0<d+y := by linarith
  have hm : (d-y)/(d+y)*(y/d)<1 := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hd).mpr
    simp only [one_mul]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hdy).mpr
    nlinarith only [sq_pos_of_pos hd, sq_nonneg y]
  have hh := Real.arctan_add hm
  have he : ((d-y)/(d+y)+y/d)/(1-(d-y)/(d+y)*(y/d))=1 := by
    have hn : 1-(d-y)/(d+y)*(y/d)≠0 := by linarith only [hm]
    apply (div_eq_one_iff_eq hn).mpr
    field_simp
    ring
  rw [he, Real.arctan_one] at hh
  linarith only [hh]

end ZudilinZeta
end

-- Component: Params13PhaseFormula
section
namespace ZudilinZeta

lemma f0_params13_im_formula (τ : ℂ) (hx : 87 ≤ τ.re ∧ τ.re ≤ 88)
    (hy : 0<τ.im) (hyd : τ.im<91-τ.re) :
    (f0 params13 τ).im = -273*Real.pi/4 +
      273*Real.arctan ((91-τ.re-τ.im)/(91-τ.re+τ.im)) +
      3*(27*Real.arctan (τ.im/(τ.re-27))-64*Real.arctan (τ.im/(τ.re-64))) +
      ∑ j ∈ Finset.Icc (29 : ℕ) 38,
        ((j : ℝ)*Real.arctan (τ.im/(τ.re-j))-
          (91-j)*Real.arctan (τ.im/(τ.re-91+j))) := by
  have hfirst : ((91 : ℂ)-τ).arg = -Real.pi/4+
      Real.arctan ((91-τ.re-τ.im)/(91-τ.re+τ.im)) := by
    rw [arg_eq_arctan_of_re_pos _ (by norm_num; linarith only [hx.2])]
    norm_num [Complex.sub_im, Complex.sub_re, neg_div, Real.arctan_neg]
    rw [arctan_complement_quarter τ.im (91-τ.re) hy hyd]
    ring
  norm_num [f0, params13, eta13, Finset.sum_Icc_succ_top, Complex.mul_im,
    Complex.log_im]
  rw [hfirst]
  repeat' rw [arg_eq_arctan_of_re_pos _ (by norm_num; linarith only [hx.1])]
  norm_num [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im]
  ring

end ZudilinZeta
end

-- Component: Params13SaddlePhase
section
namespace ZudilinZeta

-- The generator supplies rational witnesses only. Every inequality is kernel checked.
lemma f0_params13_im_between (τ : ℂ)
    (hx : 874790/10000 ≤ τ.re ∧ τ.re ≤ 874791/10000)
    (hy : 332820/100000 ≤ τ.im ∧ τ.im ≤ 332821/100000) :
    -87*Real.pi < (f0 params13 τ).im ∧ (f0 params13 τ).im < -86*Real.pi := by
  have h27 : 54975/1000000 ≤ Real.arctan (τ.im/(τ.re-27)) ∧
      Real.arctan (τ.im/(τ.re-27)) ≤ 54976/1000000 := by
    refine arctan_rational_enclosure _ (3698/67199) (332821/6047900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h29 : 56851/1000000 ≤ Real.arctan (τ.im/(τ.re-29)) ∧
      Real.arctan (τ.im/(τ.re-29)) ≤ 56852/1000000 := by
    refine arctan_rational_enclosure _ (33282/584791) (332821/5847900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h30 : 57838/1000000 ≤ Real.arctan (τ.im/(τ.re-30)) ∧
      Real.arctan (τ.im/(τ.re-30)) ≤ 57839/1000000 := by
    refine arctan_rational_enclosure _ (11094/191597) (332821/5747900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h31 : 58859/1000000 ≤ Real.arctan (τ.im/(τ.re-31)) ∧
      Real.arctan (τ.im/(τ.re-31)) ≤ 58861/1000000 := by
    refine arctan_rational_enclosure _ (33282/564791) (332821/5647900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h32 : 59918/1000000 ≤ Real.arctan (τ.im/(τ.re-32)) ∧
      Real.arctan (τ.im/(τ.re-32)) ≤ 59919/1000000 := by
    refine arctan_rational_enclosure _ (33282/554791) (332821/5547900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h33 : 61015/1000000 ≤ Real.arctan (τ.im/(τ.re-33)) ∧
      Real.arctan (τ.im/(τ.re-33)) ≤ 61016/1000000 := by
    refine arctan_rational_enclosure _ (11094/181597) (332821/5447900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h34 : 62153/1000000 ≤ Real.arctan (τ.im/(τ.re-34)) ∧
      Real.arctan (τ.im/(τ.re-34)) ≤ 62154/1000000 := by
    refine arctan_rational_enclosure _ (774/12437) (332821/5347900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h35 : 63334/1000000 ≤ Real.arctan (τ.im/(τ.re-35)) ∧
      Real.arctan (τ.im/(τ.re-35)) ≤ 63336/1000000 := by
    refine arctan_rational_enclosure _ (33282/524791) (332821/5247900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h36 : 64561/1000000 ≤ Real.arctan (τ.im/(τ.re-36)) ∧
      Real.arctan (τ.im/(τ.re-36)) ≤ 64562/1000000 := by
    refine arctan_rational_enclosure _ (3698/57199) (332821/5147900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h37 : 65836/1000000 ≤ Real.arctan (τ.im/(τ.re-37)) ∧
      Real.arctan (τ.im/(τ.re-37)) ≤ 65838/1000000 := by
    refine arctan_rational_enclosure _ (33282/504791) (332821/5047900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h38 : 67163/1000000 ≤ Real.arctan (τ.im/(τ.re-38)) ∧
      Real.arctan (τ.im/(τ.re-38)) ≤ 67164/1000000 := by
    refine arctan_rational_enclosure _ (33282/494791) (332821/4947900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h53 : 96228/1000000 ≤ Real.arctan (τ.im/(τ.re-53)) ∧
      Real.arctan (τ.im/(τ.re-53)) ≤ 96231/1000000 := by
    refine arctan_rational_enclosure _ (33282/344791) (332821/3447900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h54 : 99083/1000000 ≤ Real.arctan (τ.im/(τ.re-54)) ∧
      Real.arctan (τ.im/(τ.re-54)) ≤ 99087/1000000 := by
    refine arctan_rational_enclosure _ (3698/37199) (332821/3347900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h55 : 102113/1000000 ≤ Real.arctan (τ.im/(τ.re-55)) ∧
      Real.arctan (τ.im/(τ.re-55)) ≤ 102117/1000000 := by
    refine arctan_rational_enclosure _ (33282/324791) (332821/3247900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h56 : 105333/1000000 ≤ Real.arctan (τ.im/(τ.re-56)) ∧
      Real.arctan (τ.im/(τ.re-56)) ≤ 105337/1000000 := by
    refine arctan_rational_enclosure _ (33282/314791) (332821/3147900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h57 : 108762/1000000 ≤ Real.arctan (τ.im/(τ.re-57)) ∧
      Real.arctan (τ.im/(τ.re-57)) ≤ 108766/1000000 := by
    refine arctan_rational_enclosure _ (11094/101597) (332821/3047900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h58 : 112420/1000000 ≤ Real.arctan (τ.im/(τ.re-58)) ∧
      Real.arctan (τ.im/(τ.re-58)) ≤ 112426/1000000 := by
    refine arctan_rational_enclosure _ (33282/294791) (332821/2947900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h59 : 116332/1000000 ≤ Real.arctan (τ.im/(τ.re-59)) ∧
      Real.arctan (τ.im/(τ.re-59)) ≤ 116338/1000000 := by
    refine arctan_rational_enclosure _ (33282/284791) (332821/2847900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h60 : 120525/1000000 ≤ Real.arctan (τ.im/(τ.re-60)) ∧
      Real.arctan (τ.im/(τ.re-60)) ≤ 120532/1000000 := by
    refine arctan_rational_enclosure _ (11094/91597) (332821/2747900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h61 : 125029/1000000 ≤ Real.arctan (τ.im/(τ.re-61)) ∧
      Real.arctan (τ.im/(τ.re-61)) ≤ 125037/1000000 := by
    refine arctan_rational_enclosure _ (33282/264791) (332821/2647900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h62 : 129881/1000000 ≤ Real.arctan (τ.im/(τ.re-62)) ∧
      Real.arctan (τ.im/(τ.re-62)) ≤ 129891/1000000 := by
    refine arctan_rational_enclosure _ (33282/254791) (332821/2547900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have h64 : 140802/1000000 ≤ Real.arctan (τ.im/(τ.re-64)) ∧
      Real.arctan (τ.im/(τ.re-64)) ≤ 140815/1000000 := by
    refine arctan_rational_enclosure _ (33282/234791) (332821/2347900) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.2, hy.1]
    · apply (div_le_iff₀ (by linarith only [hx.1])).mpr
      nlinarith only [hx.1, hy.2]
  have ht : 28126/1000000 ≤ Real.arctan ((91-τ.re-τ.im)/(91-τ.re+τ.im)) ∧
      Real.arctan ((91-τ.re-τ.im)/(91-τ.re+τ.im)) ≤ 28142/1000000 := by
    refine arctan_rational_enclosure _ (19269/684911) (482/17123) _ _
      (by norm_num) ⟨?_, ?_⟩ (by norm_num) (by norm_num)
    · apply (le_div_iff₀ (by linarith only [hx.2, hy.1])).mpr
      nlinarith only [hx.2, hy.2]
    · apply (div_le_iff₀ (by linarith only [hx.2, hy.1])).mpr
      nlinarith only [hx.1, hy.1]
  have he := f0_params13_im_formula τ
    ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
    (by linarith only [hy.1]) (by linarith only [hx.2, hy.2])
  norm_num [Finset.sum_Icc_succ_top] at he
  ring_nf at he h27 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h53 h54 h55 h56 h57 h58 h59 h60 h61 h62 h64 ht
  constructor <;> linarith only [he, Real.pi_gt_d4, Real.pi_lt_d4, h27.1, h27.2, h29.1, h29.2, h30.1, h30.2, h31.1, h31.2, h32.1, h32.2, h33.1, h33.2, h34.1, h34.2, h35.1, h35.2, h36.1, h36.2, h37.1, h37.2, h38.1, h38.2, h53.1, h53.2, h54.1, h54.2, h55.1, h55.2, h56.1, h56.2, h57.1, h57.2, h58.1, h58.2, h59.1, h59.2, h60.1, h60.2, h61.1, h61.2, h62.1, h62.2, h64.1, h64.2, ht.1, ht.2]

lemma f0_params13_phase_nonresonant (τ : ℂ)
    (hx : 874790/10000 ≤ τ.re ∧ τ.re ≤ 874791/10000)
    (hy : 332820/100000 ≤ τ.im ∧ τ.im ≤ 332821/100000) :
    ∀ k : ℤ, (f0 params13 τ).im ≠ (k : ℝ)*Real.pi := by
  obtain ⟨hl, hu⟩ := f0_params13_im_between τ hx hy
  intro k hk
  rw [hk] at hl hu
  have hkl : (-87 : ℝ) < k := (mul_lt_mul_iff_left₀ Real.pi_pos).mp hl
  have hku : (k : ℝ) < -86 := (mul_lt_mul_iff_left₀ Real.pi_pos).mp hu
  have hkl : (-87 : ℤ) < k := by exact_mod_cast hkl
  have hku : k < (-86 : ℤ) := by exact_mod_cast hku
  omega

end ZudilinZeta
end

-- Component: Params13SaddleRoot
section
open ZudilinZeta

theorem solution :
    ∃ τ₀ : ℂ, charPoly params13 τ₀ = 0 ∧ 0 < τ₀.im ∧
      (∀ τ : ℂ, charPoly params13 τ = 0 → 0 < τ.im → τ.re ≤ τ₀.re) ∧
      τ₀.re < (params13.eta 0 : ℝ) ∧
      (∀ k : ℤ, (f0 params13 τ₀).im ≠ (k : ℝ) * Real.pi) := by
  obtain ⟨τ, hroot, him, hmax, hx, hy⟩ := saddle_root_params13_geometry
  refine ⟨τ, hroot, him, hmax, ?_, ?_⟩
  · norm_num [params13, eta13]
    linarith only [hx.2]
  · exact f0_params13_phase_nonresonant τ
      ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
      ⟨by linarith only [hy.1], by linarith only [hy.2]⟩
end
