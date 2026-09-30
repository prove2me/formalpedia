-- Prove2me | solution 1 for WeierstrassEllipticZeta.projective_extension_addition_regular
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-24T04:51:54.422303+00:00
-- url     : https://prove2.me/submissions/0417b206-413d-4c7b-a04f-2a07950a8b1b

import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_frobenius_stickelberger
import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_nondegenerate
import Theorems.Thm_WeierstrassEllipticZeta_wp_addition_formula
import Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel
import Definitions.Def_TranscendenceTheory_GraphQuotientExtension
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Definitions.Def_WeierstrassEllipticZeta_Defs
import Mathlib.Analysis.Calculus.Deriv.Inverse


noncomputable section

open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

/-- Each fiber of `℘` is isolated away from the lattice. The identity theorem
rules out a constant germ because `℘` has a double pole at zero. -/
lemma weierstrassP_eventually_ne (L : PeriodPair) (v c : ℂ) (hv : v ∉ L.lattice) :
    ∀ᶠ w in 𝓝[≠] v, L.weierstrassP w ≠ c := by
  by_contra h
  have hf : ∃ᶠ w in 𝓝[≠] v, L.weierstrassP w = c := by simpa using h
  have hconnected : IsPreconnected (L.lattice : Set ℂ)ᶜ :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
  have heq : Set.EqOn L.weierstrassP (fun _ ↦ c) L.latticeᶜ :=
    L.analyticOnNhd_weierstrassP.eqOn_of_preconnected_of_frequently_eq
      (fun _ _ ↦ analyticAt_const) hconnected hv hf
  have hregular : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∉ L.lattice := by
    have hnhds : ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ ((L.lattice : Set ℂ) \ {0})ᶜ :=
      L.compl_lattice_sdiff_singleton_mem_nhds 0
    filter_upwards [hnhds.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hw hw0
    intro hwL
    exact hw ⟨hwL, hw0⟩
  have hnear : L.weierstrassP =ᶠ[𝓝[≠] (0 : ℂ)] (fun _ ↦ c) :=
    hregular.mono fun w hw ↦ heq hw
  have ho := meromorphicOrderAt_congr hnear
  rw [L.order_weierstrassP 0 L.lattice.zero_mem, meromorphicOrderAt_const] at ho
  split_ifs at ho <;> norm_num at ho

/-- Once the classical divided addition formula is proved for distinct `℘`
values, continuity supplies the full milestone, including coincident values. -/
theorem zeta_addition_of_nondegenerate
    (hgeneric : ∀ (L : PeriodPair) (z v : ℂ), z ∉ L.lattice → v ∉ L.lattice →
      z + v ∉ L.lattice → L.weierstrassP v ≠ L.weierstrassP z →
      weierstrassZeta L (z + v) = weierstrassZeta L z + weierstrassZeta L v +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) /
          (2 * (L.weierstrassP v - L.weierstrassP z)))
    (L : PeriodPair) (z v : ℂ) (hz : z ∉ L.lattice) (hv : v ∉ L.lattice)
    (hzv : z + v ∉ L.lattice) :
    2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
      2 * (weierstrassZeta L z + weierstrassZeta L v) *
        (L.weierstrassP v - L.weierstrassP z) +
      L.derivWeierstrassP v - L.derivWeierstrassP z := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hP := (L.differentiableOn_weierstrassP.differentiableAt (hopen.mem_nhds hv)).continuousAt
  have hD := (L.differentiableOn_derivWeierstrassP.differentiableAt
    (hopen.mem_nhds hv)).continuousAt
  have hZ := (hasDerivAt_weierstrassZeta L v hv).continuousAt
  have hZv := (hasDerivAt_weierstrassZeta L (z + v) hzv).continuousAt.comp
    (continuousAt_const.add continuousAt_id)
  have hleft : ContinuousAt (fun w ↦
      2 * (L.weierstrassP w - L.weierstrassP z) * weierstrassZeta L (z + w)) v :=
    (continuousAt_const.mul (hP.sub continuousAt_const)).mul hZv
  have hright : ContinuousAt (fun w ↦
      2 * (weierstrassZeta L z + weierstrassZeta L w) *
        (L.weierstrassP w - L.weierstrassP z) +
      L.derivWeierstrassP w - L.derivWeierstrassP z) v :=
    (((continuousAt_const.mul (continuousAt_const.add hZ)).mul
      (hP.sub continuousAt_const)).add hD).sub continuousAt_const
  have hvnear : ∀ᶠ w in 𝓝 v, w ∉ L.lattice := hopen.mem_nhds hv
  have hzvnear : ∀ᶠ w in 𝓝 v, z + w ∉ L.lattice :=
    (continuousAt_const.add continuousAt_id).eventually (hopen.mem_nhds hzv)
  have heq : (fun w ↦
      2 * (L.weierstrassP w - L.weierstrassP z) * weierstrassZeta L (z + w))
      =ᶠ[𝓝[≠] v] (fun w ↦
      2 * (weierstrassZeta L z + weierstrassZeta L w) *
        (L.weierstrassP w - L.weierstrassP z) +
      L.derivWeierstrassP w - L.derivWeierstrassP z) := by
    filter_upwards [hvnear.filter_mono nhdsWithin_le_nhds,
      hzvnear.filter_mono nhdsWithin_le_nhds,
      weierstrassP_eventually_ne L v (L.weierstrassP z) hv] with w hw hzw hne
    rw [hgeneric L z w hz hw hzw hne]
    have hdelta : L.weierstrassP w - L.weierstrassP z ≠ 0 := sub_ne_zero.mpr hne
    field_simp
    ring
  exact tendsto_nhds_unique (hleft.tendsto.mono_left nhdsWithin_le_nhds)
    ((hright.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)

end WeierstrassEllipticZeta


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

/-- A bihomogeneous `(5,5)` addition law. Its base locus on the affine
charts is exactly the equal-base-point locus. In particular it includes
opposite points with nonzero elliptic derivative. -/
def extensionAdditionVector {R : Type*} [CommRing R] (X Y : Fin 5 → R) : Fin 5 → R :=
  let Z := X 0 * Y 0
  let d := X 1 * Y 0 - Y 1 * X 0
  let t := X 2 * Y 0 - Y 2 * X 0
  let s := X 1 * Y 0 + Y 1 * X 0
  let k := X 3 * Y 0 + Y 3 * X 0
  let n := -4 * (X 2 * Y 0) * d ^ 3 +
    4 * t * (2 * X 1 * Y 0 + Y 1 * X 0) * d ^ 2 - Z * t ^ 3
  ![4 * Z ^ 2 * d ^ 3,
    Z ^ 2 * d * t ^ 2 - 4 * Z * s * d ^ 3,
    Z * n,
    4 * Z * k * d ^ 3 + 2 * Z ^ 2 * d ^ 2 * t,
    k * n - 2 * Z * (X 2 * Y 0) * t * d ^ 2 -
      2 * Z * (Y 1 * X 0) * t ^ 2 * d + 8 * s ^ 2 * d ^ 3]

theorem extensionAdditionVector_smul (X Y : Fin 5 → ℂ) (a b : ℂ) :
    extensionAdditionVector (a • X) (b • Y) =
      (a ^ 5 * b ^ 5) • extensionAdditionVector X Y := by
  ext i
  fin_cases i <;> simp [extensionAdditionVector, Pi.smul_apply, smul_eq_mul] <;> ring

theorem extensionAdditionVector_ne_zero (X Y : Fin 5 → ℂ)
    (hX : X 0 ≠ 0) (hY : Y 0 ≠ 0)
    (h : X 1 * Y 0 ≠ Y 1 * X 0 ∨ X 2 * Y 0 ≠ Y 2 * X 0) :
    extensionAdditionVector X Y ≠ 0 := by
  intro hn
  by_cases hd : X 1 * Y 0 = Y 1 * X 0
  · have ht := h.resolve_left (not_not.mpr hd)
    have hz := congrFun hn 2
    have hz' : X 2 * Y 0 - Y 2 * X 0 = 0 := by
      simpa [extensionAdditionVector, hd, hX, hY] using hz
    exact ht (sub_eq_zero.mp hz')
  · have hz := congrFun hn 0
    have hne : 4 * (X 0 * Y 0) ^ 2 * (X 1 * Y 0 - Y 1 * X 0) ^ 3 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (mul_ne_zero hX hY)))
        (pow_ne_zero _ (sub_ne_zero.mpr hd))
    exact hne hz

private theorem additionVector_affine (x y w a b c : ℂ) (hd : x - a ≠ 0) :
    extensionAdditionVector ![1, x, y, w, y * w + 2 * x ^ 2]
        ![1, a, b, c, b * c + 2 * a ^ 2] =
      (4 * (x - a) ^ 3) •
        let s := (y - b) / (2 * (x - a))
        let xx := s ^ 2 - x - a
        let yy := -y + 2 * s * (x - xx)
        let ww := w + c + s
        ![1, xx, yy, ww, yy * ww + 2 * xx ^ 2] := by
  ext i
  fin_cases i <;> simp [extensionAdditionVector, Pi.smul_apply, smul_eq_mul] <;>
    field_simp <;> ring

private lemma derivative_frobenius_identity (L : PeriodPair) (z v : ℂ)
    (hz : z ∉ L.lattice) (hv : v ∉ L.lattice) (hzv : z + v ∉ L.lattice) :
    2 * (weierstrassZeta L (z + v) - weierstrassZeta L z - weierstrassZeta L v) *
      (-L.weierstrassP (z + v) + L.weierstrassP z) =
        L.derivWeierstrassP z + L.derivWeierstrassP (z + v) := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hZ := hasDerivAt_weierstrassZeta L z hz
  have hZv : HasDerivAt (fun w ↦ weierstrassZeta L (w + v))
      (-L.weierstrassP (z + v)) z := by
    convert! (hasDerivAt_weierstrassZeta L (z + v) hzv).comp z
      ((hasDerivAt_id z).add_const v) using 1 <;> simp
  have hP : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    simpa using (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
  have hPv : HasDerivAt (fun w ↦ L.weierstrassP (w + v))
      (L.derivWeierstrassP (z + v)) z := by
    have hh : HasDerivAt L.weierstrassP (L.derivWeierstrassP (z + v)) (z + v) := by
      simpa using (L.analyticOnNhd_weierstrassP (z + v) hzv).differentiableAt.hasDerivAt
    convert! hh.comp z ((hasDerivAt_id z).add_const v) using 1 <;> simp
  have hnear : ∀ᶠ w in 𝓝 z, w ∉ L.lattice := hopen.mem_nhds hz
  have hnearv : ∀ᶠ w in 𝓝 z, w + v ∉ L.lattice :=
    (continuousAt_id.add continuousAt_const).eventually (hopen.mem_nhds hzv)
  have heq : (fun w ↦
      (weierstrassZeta L (w + v) - weierstrassZeta L w - weierstrassZeta L v) ^ 2)
      =ᶠ[𝓝 z] (fun w ↦ L.weierstrassP w + L.weierstrassP v + L.weierstrassP (w + v)) := by
    filter_upwards [hnear, hnearv] with w hw hwv
    exact frobenius_stickelberger L w v hw hv hwv
  have hleft := ((hZv.sub hZ).sub_const (weierstrassZeta L v)).pow 2
  have hright := (hP.add_const (L.weierstrassP v)).add hPv
  have he := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  simpa only [Pi.sub_apply, Nat.cast_ofNat, show 2 - 1 = (1 : ℕ) by decide,
    pow_one, sub_neg_eq_add] using he

private theorem affine_addition_values (L : PeriodPair) (z v : ℂ)
    (hz : z ∉ L.lattice) (hv : v ∉ L.lattice) (hzv : z + v ∉ L.lattice)
    (hd : L.weierstrassP z - L.weierstrassP v ≠ 0) :
    let s := (L.derivWeierstrassP z - L.derivWeierstrassP v) /
      (2 * (L.weierstrassP z - L.weierstrassP v))
    L.weierstrassP (z + v) = s ^ 2 - L.weierstrassP z - L.weierstrassP v ∧
    L.derivWeierstrassP (z + v) = -L.derivWeierstrassP z +
      2 * s * (L.weierstrassP z - L.weierstrassP (z + v)) ∧
    weierstrassZeta L (z + v) = weierstrassZeta L z + weierstrassZeta L v + s := by
  dsimp only
  have hζ := zeta_addition_nondegenerate L v z hv hz
    (by simpa [add_comm] using hzv) (sub_ne_zero.mp hd)
  rw [add_comm v z, add_comm (weierstrassZeta L v)] at hζ
  have hwp := wp_addition_formula L v z hv hz
    (by simpa [add_comm] using hzv)
  rw [add_comm v z] at hwp
  have hder := derivative_frobenius_identity L z v hz hv hzv
  rw [hζ] at hder
  refine ⟨?_, ?_, hζ⟩
  · field_simp
    linear_combination hwp
  · linear_combination -hder

private theorem exists_generic_addition_point (L : PeriodPair) (v : ℂ) :
    ∃ z : ℂ, z ∉ L.lattice ∧ z + v ∉ L.lattice ∧
      L.weierstrassP z - L.weierstrassP v ≠ 0 := by
  let a := L.ω₁ / 2
  have ha : a ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have hnear : ∀ᶠ z in 𝓝 a, z ∉ L.lattice := L.isClosed_lattice.isOpen_compl.mem_nhds ha
  have h1 : ∀ᶠ z in 𝓝[≠] a, z ∉ L.lattice := hnear.filter_mono nhdsWithin_le_nhds
  have h2 : ∀ᶠ z in 𝓝[≠] a, z + v ∉ L.lattice := by
    have h := (continuousAt_id.add continuousAt_const).eventually
      (L.compl_lattice_sdiff_singleton_mem_nhds (a + v))
    filter_upwards [h.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hza
    intro hzL
    exact hz ⟨hzL, fun he => hza (add_right_cancel he)⟩
  have h3 := weierstrassP_eventually_ne L a (L.weierstrassP v) ha
  obtain ⟨z, hz, hzv, hd⟩ := (h1.and (h2.and h3)).exists
  exact ⟨z, hz, hzv, sub_ne_zero.mpr hd⟩

def entireExtensionVector (S : Fin 5 → ℂ → ℂ) (z u : ℂ) : Fin 5 → ℂ :=
  ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z]

theorem entireExtensionVector_value
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (z u : ℂ) (hz : z ∉ L.lattice) :
    entireExtensionVector S z u = (D.sigma z ^ 3) •
      ![1, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z + u,
        L.derivWeierstrassP z * (weierstrassZeta L z + u) + 2 * L.weierstrassP z ^ 2] := by
  ext j
  fin_cases j <;> simp [entireExtensionVector, hS_value z hz, Pi.smul_apply, smul_eq_mul]
    <;> ring

/-- The cleared addition identities extend across every lattice point, even
where this particular polynomial tuple vanishes. Nonvanishing is checked
separately when a tuple is used as a regular projective chart. -/
theorem entire_extension_addition_cross_products
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (z v u t : ℂ) (i j : Fin 5) :
    extensionAdditionVector (entireExtensionVector S z u) (entireExtensionVector S v t) i *
        entireExtensionVector S (z + v) (u + t) j =
      extensionAdditionVector (entireExtensionVector S z u) (entireExtensionVector S v t) j *
        entireExtensionVector S (z + v) (u + t) i := by
  let A (z v : ℂ) := extensionAdditionVector
    (entireExtensionVector S z u) (entireExtensionVector S v t)
  let B (z v : ℂ) := entireExtensionVector S (z + v) (u + t)
  have hSV (u : ℂ) (k : Fin 5) (w : ℂ) :
      AnalyticAt ℂ (fun x => entireExtensionVector S x u k) w := by
    have hs (k : Fin 5) := hS k w (Set.mem_univ w)
    fin_cases k <;> dsimp [entireExtensionVector] <;> fun_prop
  have hA1 (v : ℂ) (k : Fin 5) : AnalyticOnNhd ℂ (fun z => A z v k) Set.univ := by
    intro w _
    have hs (k : Fin 5) := hSV u k w
    fin_cases k <;> dsimp [A, extensionAdditionVector] <;> fun_prop
  have hA2 (z : ℂ) (k : Fin 5) : AnalyticOnNhd ℂ (fun v => A z v k) Set.univ := by
    intro w _
    have hs (k : Fin 5) := hSV t k w
    fin_cases k <;> dsimp [A, extensionAdditionVector] <;> fun_prop
  have hB1 (v : ℂ) (k : Fin 5) : AnalyticOnNhd ℂ (fun z => B z v k) Set.univ := by
    intro w _
    exact (hSV (u + t) k (w + v)).comp (f := fun x : ℂ => x + v) (x := w)
      (show AnalyticAt ℂ (fun x : ℂ => x + v) w from analyticAt_id.add analyticAt_const)
  have hB2 (z : ℂ) (k : Fin 5) : AnalyticOnNhd ℂ (fun v => B z v k) Set.univ := by
    intro w _
    exact (hSV (u + t) k (z + w)).comp (f := fun x : ℂ => z + x) (x := w)
      (show AnalyticAt ℂ (fun x : ℂ => z + x) w from analyticAt_const.add analyticAt_id)
  have hgeneric (z v : ℂ) (hz : z ∉ L.lattice) (hv : v ∉ L.lattice)
      (hzv : z + v ∉ L.lattice) (hd : L.weierstrassP z - L.weierstrassP v ≠ 0) :
      A z v i * B z v j = A z v j * B z v i := by
    obtain ⟨hx, hy, hw⟩ := affine_addition_values L z v hz hv hzv hd
    have hvect :
        (let s := (L.derivWeierstrassP z - L.derivWeierstrassP v) /
            (2 * (L.weierstrassP z - L.weierstrassP v))
         let xx := s ^ 2 - L.weierstrassP z - L.weierstrassP v
         let yy := -L.derivWeierstrassP z + 2 * s * (L.weierstrassP z - xx)
         let ww := (weierstrassZeta L z + u) + (weierstrassZeta L v + t) + s
         ![1, xx, yy, ww, yy * ww + 2 * xx ^ 2]) =
        ![1, L.weierstrassP (z + v), L.derivWeierstrassP (z + v),
          weierstrassZeta L (z + v) + (u + t),
          L.derivWeierstrassP (z + v) * (weierstrassZeta L (z + v) + (u + t)) +
            2 * L.weierstrassP (z + v) ^ 2] := by
      dsimp only
      have hww : (weierstrassZeta L z + u) + (weierstrassZeta L v + t) +
          (L.derivWeierstrassP z - L.derivWeierstrassP v) /
            (2 * (L.weierstrassP z - L.weierstrassP v)) =
          weierstrassZeta L (z + v) + (u + t) := by rw [hw]; ring
      rw [← hx, ← hy, hww]
    dsimp [A, B]
    rw [entireExtensionVector_value L D S hS_value z u hz,
      entireExtensionVector_value L D S hS_value v t hv,
      entireExtensionVector_value L D S hS_value (z + v) (u + t) hzv,
      extensionAdditionVector_smul, additionVector_affine _ _ _ _ _ _ hd, hvect]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hfirst (v : ℂ) (hv : v ∉ L.lattice) :
      (fun z => A z v i * B z v j) = (fun z => A z v j * B z v i) := by
    obtain ⟨a, ha, hav, had⟩ := exists_generic_addition_point L v
    apply AnalyticOnNhd.eq_of_eventuallyEq ((hA1 v i).mul (hB1 v j))
      ((hA1 v j).mul (hB1 v i)) (z₀ := a)
    have hn := L.isClosed_lattice.isOpen_compl.mem_nhds ha
    have hnv := (continuousAt_id.add continuousAt_const).eventually
      (L.isClosed_lattice.isOpen_compl.mem_nhds hav)
    have hnd := ((L.analyticOnNhd_weierstrassP a ha).continuousAt.sub
      continuousAt_const).eventually_ne had
    filter_upwards [hn, hnv, hnd] with z hz hzv hd
    exact hgeneric z v hz hv hzv hd
  have hsecond : (fun v => A z v i * B z v j) = (fun v => A z v j * B z v i) := by
    apply AnalyticOnNhd.eq_of_eventuallyEq ((hA2 z i).mul (hB2 z j))
      ((hA2 z j).mul (hB2 z i)) (z₀ := L.ω₁ / 2)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      L.ω₁_div_two_notMem_lattice] with v hv
    exact congrFun (hfirst v hv) z
  exact congrFun hsecond v


end WeierstrassEllipticZeta


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity
universe u
namespace MultiProjectiveSpace

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem IsHomogeneous.mul {P Q : M.CoordinateRing} {D E : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q E) :
    M.IsHomogeneous (P * Q) (D + E) := by
  classical
  intro d hd i
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hd)
  simpa only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hP a ha i,
    hQ b hb i]

theorem isHomogeneous_one : M.IsHomogeneous 1 0 := by
  classical
  intro d hd i
  have hd0 : d = 0 := by simpa using hd
  simp [hd0]

theorem isOpen_basic (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsOpen _ M.zariskiTopology {x | M.eval P x ≠ 0} := by
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨P, D, hP, rfl⟩

theorem isClosed_zero (P : M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hP : M.IsHomogeneous P D) :
    @IsClosed _ M.zariskiTopology {x | M.eval P x = 0} := by
  letI := M.zariskiTopology
  simpa only [Set.compl_setOf, not_not] using (M.isOpen_basic P D hP).isClosed_compl

theorem isTopologicalBasis_basic :
    @TopologicalSpace.IsTopologicalBasis _ M.zariskiTopology
      {U | ∃ P : M.CoordinateRing, ∃ D, M.IsHomogeneous P D ∧
        U = {x | M.eval P x ≠ 0}} := by
  classical
  letI := M.zariskiTopology
  have h := TopologicalSpace.isTopologicalBasis_of_subbasis_of_inter
    (show M.zariskiTopology = TopologicalSpace.generateFrom _ from rfl) (by
      rintro U ⟨P, D, hP, rfl⟩ V ⟨Q, E, hQ, rfl⟩
      refine ⟨P * Q, D + E, hP.mul M hQ, ?_⟩
      ext x
      simp [eval, mul_ne_zero_iff])
  have huniv : Set.univ ∈ {U | ∃ P : M.CoordinateRing, ∃ D,
      M.IsHomogeneous P D ∧ U = {x | M.eval P x ≠ 0}} := by
    refine ⟨1, 0, M.isHomogeneous_one, ?_⟩
    ext x
    simp [eval]
  simpa only [Set.insert_eq_of_mem huniv] using h

theorem eval_eq_zero_of_mem_vanishingIdeal {S : Set M.Point}
    {P : M.CoordinateRing} (hP : P ∈ M.vanishingIdeal S)
    {x : M.Point} (hx : x ∈ S) : M.eval P x = 0 := by
  have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
    apply Ideal.span_le.mpr
    rintro Q ⟨_, hQ⟩
    exact hQ x hx
  exact hle hP

theorem vanishingIdeal_antitone {S T : Set M.Point} (h : S ⊆ T) :
    M.vanishingIdeal T ≤ M.vanishingIdeal S := by
  apply Ideal.span_mono
  rintro P ⟨hP, hz⟩
  exact ⟨hP, fun x hx => hz x (h hx)⟩

theorem isClosed_zeroLocus_vanishingIdeal (S : Set M.Point) :
    @IsClosed _ M.zariskiTopology (M.zeroLocus (M.vanishingIdeal S)) := by
  letI := M.zariskiTopology
  have hset : M.zeroLocus (M.vanishingIdeal S) =
      ⋂ P : {P : M.CoordinateRing // (∃ D, M.IsHomogeneous P D) ∧
        ∀ x ∈ S, M.eval P x = 0}, {x | M.eval P.val x = 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq, zeroLocus]
    constructor
    · intro hx P
      exact hx P (Ideal.subset_span P.property)
    · intro hx P hP
      have hle : M.vanishingIdeal S ≤ RingHom.ker (MvPolynomial.eval (M.coordinate x)) := by
        apply Ideal.span_le.mpr
        intro Q hQ
        exact hx ⟨Q, hQ⟩
      exact hle hP
  rw [hset]
  apply isClosed_iInter
  intro P
  obtain ⟨D, hD⟩ := P.property.1
  exact M.isClosed_zero P.val D hD

/-- The chosen-representative ideal agrees with Zariski closure. -/
theorem zeroLocus_vanishingIdeal_eq_closure (S : Set M.Point) :
    M.zeroLocus (M.vanishingIdeal S) = @closure _ M.zariskiTopology S := by
  letI := M.zariskiTopology
  apply Set.Subset.antisymm
  · intro x hx
    apply M.isTopologicalBasis_basic.mem_closure_iff.mpr
    rintro U ⟨P, D, hP, rfl⟩ hxU
    by_contra hn
    have hPS : ∀ y ∈ S, M.eval P y = 0 := by
      intro y hy
      by_contra hp
      exact hn ⟨y, hp, hy⟩
    exact hxU (hx P (Ideal.subset_span ⟨⟨D, hP⟩, hPS⟩))
  · apply closure_minimal
    · intro x hx P hP
      exact M.eval_eq_zero_of_mem_vanishingIdeal hP hx
    · exact M.isClosed_zeroLocus_vanishingIdeal S

end MultiProjectiveSpace

theorem singleBlock_isHomogeneous {K : Type*} [Field K] {N d : ℕ}
    {P : MvPolynomial (Fin (N + 1)) K} (hP : P.IsHomogeneous d) :
    (projectiveSpace K N).IsHomogeneous
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) P) (fun _ => d) := by
  classical
  intro a ha i
  have h := hP.rename_isHomogeneous (f := fun j => (⟨(0 : Fin 1), j⟩ :
    (projectiveSpace K N).Variable)) (MvPolynomial.mem_support_iff.mp ha)
  change Finsupp.weight (1 : (projectiveSpace K N).Variable → ℕ) a = d at h
  rw [Finsupp.weight_eq_sum] at h
  simp only [Pi.one_apply, smul_eq_mul, mul_one] at h
  rw [Fintype.sum_sigma] at h
  change (∑ x : Fin 1, ∑ y : Fin (N + 1), a ⟨x, y⟩) = d at h
  change Fin 1 at i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  change (∑ j : Fin (N + 1), a ⟨(0 : Fin 1), j⟩) = d
  exact (Fin.sum_univ_one _).symm.trans h

theorem projective_isClosed_zero {K : Type*} [Field K] {N d : ℕ}
    {P : MvPolynomial (Fin (N + 1)) K} (hP : P.IsHomogeneous d) :
    @IsClosed _
      (TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
        (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology)
      {p | MvPolynomial.eval p.rep P = 0} := by
  letI := (projectiveSpace K N).zariskiTopology
  letI := TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
    (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology
  have hcont : @Continuous _ (projectiveSpace K N).Point _ (projectiveSpace K N).zariskiTopology
      (fun (p : Projectivization K (Fin (N + 1) → K)) =>
      (fun _ => p : (projectiveSpace K N).Point)) := continuous_induced_dom
  have h := ((projectiveSpace K N).isClosed_zero _ _
    (singleBlock_isHomogeneous hP)).preimage hcont
  convert h using 1
  ext p
  change MvPolynomial.eval p.rep P = 0 ↔
    (projectiveSpace K N).eval
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) P) (fun _ => p) = 0
  simp only [MultiProjectiveSpace.eval, MvPolynomial.eval_rename]
  rfl

theorem projective_isOpen_coordinate {K : Type*} [Field K] {N : ℕ}
    (j : Fin (N + 1)) :
    @IsOpen _
      (TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
        (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology)
      {p | p.rep j ≠ 0} := by
  letI := (projectiveSpace K N).zariskiTopology
  letI := TopologicalSpace.induced (fun (p : Projectivization K (Fin (N + 1) → K)) =>
    (fun _ => p : (projectiveSpace K N).Point)) (projectiveSpace K N).zariskiTopology
  have hcont : @Continuous _ (projectiveSpace K N).Point _ (projectiveSpace K N).zariskiTopology
      (fun (p : Projectivization K (Fin (N + 1) → K)) =>
      (fun _ => p : (projectiveSpace K N).Point)) := continuous_induced_dom
  have h := ((projectiveSpace K N).isOpen_basic _ _
    (singleBlock_isHomogeneous (MvPolynomial.isHomogeneous_X K j))).preimage
      hcont
  convert h using 1
  ext p
  change p.rep j ≠ 0 ↔
    (projectiveSpace K N).eval
      (MvPolynomial.rename (fun j => ⟨(0 : Fin 1), j⟩) (MvPolynomial.X j)) (fun _ => p) ≠ 0
  simp [MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate]

theorem projective_regular_of_homogeneous
    {K X : Type u} [Field K] {N N' d : ℕ}
    (e : X → Projectivization K (Fin (N + 1) → K))
    (f : X → Projectivization K (Fin (N' + 1) → K))
    (P : Fin (N' + 1) → MvPolynomial (Fin (N + 1)) K)
    (hP : ∀ j, (P j).IsHomogeneous d)
    (hf : ∀ x, ∃ h : (fun j => MvPolynomial.eval (e x).rep (P j)) ≠ 0,
      Projectivization.mk K (fun j => MvPolynomial.eval (e x).rep (P j)) h = f x) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace K N) (projectiveSpace K N')
      (fun x => fun _ => e x) (fun x => fun _ => f x) := by
  letI := (projectiveSpace K N).zariskiTopology
  intro x b
  let Q : Fin (N' + 1) → (projectiveSpace K N).CoordinateRing :=
    fun j => MvPolynomial.rename (fun k => ⟨(0 : Fin 1), k⟩) (P j)
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => d,
    Q,
    (fun j => singleBlock_isHomogeneous (hP j)), ?_⟩
  intro y _
  have heq : (fun j => (projectiveSpace K N).eval (Q j) (fun _ => e y)) =
      (fun j => MvPolynomial.eval (e y).rep (P j)) := by
    ext j
    change MvPolynomial.eval _ (MvPolynomial.rename _ (P j)) = _
    rw [MvPolynomial.eval_rename]
    rfl
  obtain ⟨hne, hmk⟩ := hf y
  change ∃ h : (fun j : Fin (N' + 1) =>
      (projectiveSpace K N).eval (Q j) (fun _ => e y)) ≠ 0,
    Projectivization.mk K
      (fun j : Fin (N' + 1) => (projectiveSpace K N).eval (Q j) (fun _ => e y)) h = f y
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hne
  · simpa only [heq] using hmk

end PhilipponMultiplicity

namespace WeierstrassEllipticZeta
open PhilipponMultiplicity

theorem projective_extension_locallyClosed (g₂ g₃ : ℂ) :
    @IsLocallyClosed _
      (TopologicalSpace.induced (fun p _ => p) (projectiveSpace ℂ 4).zariskiTopology)
      {p : Projectivization ℂ (Fin 5 → ℂ) |
        MvPolynomial.eval p.rep extensionQuadric = 0 ∧
        MvPolynomial.eval p.rep (extensionCubic g₂ g₃) = 0 ∧
        (p.rep 0 ≠ 0 ∨ p.rep 2 ≠ 0)} := by
  letI := TopologicalSpace.induced (fun (p : Projectivization ℂ (Fin 5 → ℂ)) =>
    (fun _ => p : (projectiveSpace ℂ 4).Point)) (projectiveSpace ℂ 4).zariskiTopology
  have hq : extensionQuadric.IsHomogeneous 2 := by
    exact ((MvPolynomial.isHomogeneous_X ℂ 0).mul
      (MvPolynomial.isHomogeneous_X ℂ 4)).sub
      ((MvPolynomial.isHomogeneous_X ℂ 2).mul (MvPolynomial.isHomogeneous_X ℂ 3)) |>.sub
        (MvPolynomial.isHomogeneous_C_mul_X_pow 2 1 2)
  have hc : (extensionCubic g₂ g₃).IsHomogeneous 3 := by
    exact (((MvPolynomial.isHomogeneous_X ℂ 0).mul
      (MvPolynomial.isHomogeneous_X_pow 2 2)).sub
      (MvPolynomial.isHomogeneous_C_mul_X_pow 4 1 3)).add
        ((MvPolynomial.isHomogeneous_C_mul_X_pow g₂ 0 2).mul
          (MvPolynomial.isHomogeneous_X ℂ 1)) |>.add
        (MvPolynomial.isHomogeneous_C_mul_X_pow g₃ 0 3)
  convert
    ((projective_isClosed_zero hq).inter (projective_isClosed_zero hc)).isLocallyClosed.inter
      ((projective_isOpen_coordinate (K := ℂ) (0 : Fin 5)).union
        (projective_isOpen_coordinate (K := ℂ) (2 : Fin 5))).isLocallyClosed using 1
  ext p
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, and_assoc]

theorem projective_extension_fiber_action_regular (g₂ g₃ u : ℂ)
    (F : ProjectiveExtensionFiberModel g₂ g₃) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace ℂ 4) (projectiveSpace ℂ 4)
      (fun p : ProjectiveExtensionChartLocus g₂ g₃ => fun _ => extensionProjectivePoint p)
      (fun p => fun _ => extensionProjectivePoint (F.action u p)) := by
  let P : Fin 5 → MvPolynomial (Fin 5) ℂ :=
    ![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2,
      MvPolynomial.X 3 + MvPolynomial.C u * MvPolynomial.X 0,
      MvPolynomial.X 4 + MvPolynomial.C u * MvPolynomial.X 2]
  apply projective_regular_of_homogeneous _ _ P (d := 1)
  · intro j
    fin_cases j
    · exact MvPolynomial.isHomogeneous_X ℂ 0
    · exact MvPolynomial.isHomogeneous_X ℂ 1
    · exact MvPolynomial.isHomogeneous_X ℂ 2
    · exact (MvPolynomial.isHomogeneous_X ℂ 3).add
        ((MvPolynomial.isHomogeneous_C (Fin 5) u).mul (MvPolynomial.isHomogeneous_X ℂ 0))
    · exact (MvPolynomial.isHomogeneous_X ℂ 4).add
        ((MvPolynomial.isHomogeneous_C (Fin 5) u).mul (MvPolynomial.isHomogeneous_X ℂ 2))
  · intro p
    have heq : (fun j => MvPolynomial.eval (extensionProjectivePoint p).rep (P j)) =
        extensionFiberShear u (extensionProjectivePoint p).rep := by
      ext j
      fin_cases j <;> simp [P, extensionFiberShear]
    obtain ⟨h, hh⟩ := F.action_coords u p
    exact ⟨by simpa only [heq] using h, by simpa only [heq] using hh.symm⟩

end WeierstrassEllipticZeta


set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem isHomogeneous_X (v : M.Variable) :
    M.IsHomogeneous (MvPolynomial.X v) (fun i => if i = v.1 then 1 else 0) := by
  classical
  intro a ha i
  simp only [MvPolynomial.support_X, Finset.mem_singleton] at ha
  subst a
  rcases v with ⟨b, j⟩
  by_cases hi : i = b
  · subst i
    simp [Finsupp.single_apply, Sigma.mk.inj_iff]
  · have hn (k : Fin (M.ambientDimension i + 1)) :
        (⟨b, j⟩ : M.Variable) ≠ ⟨i, k⟩ := by
      intro h
      exact hi (congrArg Sigma.fst h).symm
    simp [Finsupp.single_apply, hi, hn]

theorem isHomogeneous_C (c : K) : M.IsHomogeneous (MvPolynomial.C c) 0 := by
  classical
  intro a ha i
  have ha0 : a = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ha)
  simp [ha0]

theorem IsHomogeneous.add {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P + Q) D := by
  classical
  intro a ha i
  rcases Finset.mem_union.mp (MvPolynomial.support_add ha) with h | h
  · exact hP a h i
  · exact hQ a h i

theorem IsHomogeneous.neg {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) : M.IsHomogeneous (-P) D := by
  intro a ha i
  exact hP a (by simpa only [MvPolynomial.support_neg] using ha) i

theorem IsHomogeneous.sub {P Q : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (hQ : M.IsHomogeneous Q D) :
    M.IsHomogeneous (P - Q) D := by
  simpa only [sub_eq_add_neg] using hP.add M (hQ.neg M)

theorem IsHomogeneous.C_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : K) : M.IsHomogeneous (MvPolynomial.C c * P) D := by
  simpa only [zero_add] using (M.isHomogeneous_C c).mul M hP

theorem IsHomogeneous.nat_mul {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (c : ℕ) : M.IsHomogeneous (c * P) D := by
  simpa only [map_natCast] using hP.C_mul M (c : K)

theorem IsHomogeneous.pow {P : M.CoordinateRing} {D : M.FactorIndex → ℕ}
    (hP : M.IsHomogeneous P D) (n : ℕ) :
    M.IsHomogeneous (P ^ n) (fun i => n * D i) := by
  induction n with
  | zero =>
    convert M.isHomogeneous_one using 1
    · simp
    · funext i; simp
  | succ n ih =>
    convert ih.mul M hP using 1
    · exact pow_succ P n
    · funext i; simp [Nat.succ_mul]

end PhilipponMultiplicity.MultiProjectiveSpace


set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open TranscendenceTheory
namespace WeierstrassEllipticZeta

theorem projective_eq_of_cross_products (X Y : Fin 5 → ℂ)
    (hX : X ≠ 0) (hY : Y ≠ 0)
    (h : ∀ i j, X i * Y j = X j * Y i) :
    Projectivization.mk ℂ X hX = Projectivization.mk ℂ Y hY := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, Y j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hY (funext hn)
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨X j / Y j, ?_⟩
  ext i
  change (X j / Y j) * Y i = X i
  field_simp
  simpa only [mul_comm] using (h i j).symm

theorem projective_extension_addition_polynomial
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (η : L.lattice →ₗ[ℤ] ℂ)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)
    (p q : ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (hn : extensionAdditionVector p.val.val.rep q.val.val.rep ≠ 0) :
    Projectivization.mk ℂ (extensionAdditionVector p.val.val.rep q.val.val.rep) hn =
      (p + q).val.val := by
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  obtain ⟨⟨z, u⟩, rfl⟩ := (extensionPeriodGraph L.lattice η).mkQ_surjective p
  obtain ⟨⟨v, t⟩, rfl⟩ := (extensionPeriodGraph L.lattice η).mkQ_surjective q
  obtain ⟨hX, hPX⟩ := he z u
  obtain ⟨hY, hPY⟩ := he v t
  obtain ⟨hB, hPB⟩ := he (z + v) (u + t)
  have hsum : e ((extensionPeriodGraph L.lattice η).mkQ (z + v, u + t)) =
      e ((extensionPeriodGraph L.lattice η).mkQ (z, u)) +
        e ((extensionPeriodGraph L.lattice η).mkQ (v, t)) := by
    change e ((extensionPeriodGraph L.lattice η).mkQ ((z, u) + (v, t))) = _
    rw [map_add, map_add]
  rw [hsum] at hPB
  rw [hPB]
  apply projective_eq_of_cross_products _ _ hn hB
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ _ hX
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ _ hY
  rw [hPX, hPY, ← ha, ← hb]
  simp only [Units.smul_def, extensionAdditionVector_smul, Pi.smul_apply, smul_eq_mul]
  intro i j
  have hc := entire_extension_addition_cross_products L D S hS hS_value z v u t i j
  change extensionAdditionVector (entireExtensionVector S z u) (entireExtensionVector S v t) i *
      entireExtensionVector S (z + v) (u + t) j = _ at hc
  dsimp only [entireExtensionVector] at hc
  have hh := congrArg (fun r => a.val ^ 5 * (b.val ^ 5 * r)) hc
  simpa only [mul_assoc] using hh

open PhilipponMultiplicity

private def extensionAdditionPolynomials :
    Fin 5 → (projectiveSquare ℂ 4).CoordinateRing :=
  extensionAdditionVector
    (fun j => MvPolynomial.X ⟨(0 : Fin 2), j⟩)
    (fun j => MvPolynomial.X ⟨(1 : Fin 2), j⟩)

private theorem extensionAdditionPolynomials_homogeneous :
    ∀ j, (projectiveSquare ℂ 4).IsHomogeneous (extensionAdditionPolynomials j) (fun _ => 5) := by
  let M := projectiveSquare ℂ 4
  let X : Fin 5 → M.CoordinateRing := fun j => MvPolynomial.X ⟨(0 : Fin 2), j⟩
  let Y : Fin 5 → M.CoordinateRing := fun j => MvPolynomial.X ⟨(1 : Fin 2), j⟩
  have hXY (a b : Fin 5) : M.IsHomogeneous (X a * Y b) (fun _ => 1) := by
    have h := (M.isHomogeneous_X ⟨(0 : Fin 2), a⟩).mul M
      (M.isHomogeneous_X ⟨(1 : Fin 2), b⟩)
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have hYX (a b : Fin 5) : M.IsHomogeneous (Y a * X b) (fun _ => 1) := by
    simpa only [mul_comm] using hXY b a
  let Z := X 0 * Y 0
  let d := X 1 * Y 0 - Y 1 * X 0
  let t := X 2 * Y 0 - Y 2 * X 0
  let s := X 1 * Y 0 + Y 1 * X 0
  let k := X 3 * Y 0 + Y 3 * X 0
  have hZ : M.IsHomogeneous Z (fun _ => 1) := hXY 0 0
  have hd : M.IsHomogeneous d (fun _ => 1) := (hXY 1 0).sub M (hYX 1 0)
  have ht : M.IsHomogeneous t (fun _ => 1) := (hXY 2 0).sub M (hYX 2 0)
  have hs : M.IsHomogeneous s (fun _ => 1) := (hXY 1 0).add M (hYX 1 0)
  have hk : M.IsHomogeneous k (fun _ => 1) := (hXY 3 0).add M (hYX 3 0)
  have hm : M.IsHomogeneous (2 * X 1 * Y 0 + Y 1 * X 0) (fun _ => 1) := by
    simpa only [mul_assoc, Nat.cast_ofNat] using
      ((hXY 1 0).nat_mul M 2).add M (hYX 1 0)
  let n := -4 * (X 2 * Y 0) * d ^ 3 +
    4 * t * (2 * X 1 * Y 0 + Y 1 * X 0) * d ^ 2 - Z * t ^ 3
  have hn : M.IsHomogeneous n (fun _ => 4) := by
    have hn0 : M.IsHomogeneous (-4 * (X 2 * Y 0) * d ^ 3) (fun _ => 4) := by
      simpa only [neg_mul, Nat.cast_ofNat, Pi.add_def, Nat.mul_one] using
        (((hXY 2 0).nat_mul M 4).neg M).mul M (hd.pow M 3)
    exact (hn0.add M
      (((ht.nat_mul M 4).mul M hm).mul M (hd.pow M 2))).sub M
        (hZ.mul M (ht.pow M 3))
  intro j
  change M.IsHomogeneous (extensionAdditionVector X Y j) (fun _ => 5)
  fin_cases j
  · exact ((hZ.pow M 2).nat_mul M 4).mul M (hd.pow M 3)
  · exact (((hZ.pow M 2).mul M hd).mul M (ht.pow M 2)).sub M
      (((hZ.nat_mul M 4).mul M hs).mul M (hd.pow M 3))
  · exact hZ.mul M hn
  · exact (((hZ.nat_mul M 4).mul M hk).mul M (hd.pow M 3)).add M
      ((((hZ.pow M 2).nat_mul M 2).mul M (hd.pow M 2)).mul M ht)
  · exact (((hk.mul M hn).sub M
      ((((hZ.nat_mul M 2).mul M (hXY 2 0)).mul M ht).mul M (hd.pow M 2))).sub M
      ((((hZ.nat_mul M 2).mul M (hYX 1 0)).mul M (ht.pow M 2)).mul M hd)).add M
      (((hs.pow M 2).nat_mul M 8).mul M (hd.pow M 3))


/-- A single polynomial law for addition on all pairs in the affine chart
with distinct elliptic base points. Opposite points are included. -/
theorem projective_extension_affine_addition_law
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (η : L.lattice →ₗ[ℤ] ℂ)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)
 :
    ∃ P : Fin 5 → (projectiveSquare ℂ 4).CoordinateRing,
      (∀ j, (projectiveSquare ℂ 4).IsHomogeneous (P j) (fun _ => 5)) ∧
      ∀ p q : ProjectiveExtensionChartLocus L.g₂ L.g₃,
        p.val.val.rep 0 ≠ 0 → q.val.val.rep 0 ≠ 0 →
        (p.val.val.rep 1 * q.val.val.rep 0 ≠ q.val.val.rep 1 * p.val.val.rep 0 ∨
         p.val.val.rep 2 * q.val.val.rep 0 ≠ q.val.val.rep 2 * p.val.val.rep 0) →
        ∃ h : (fun j => (projectiveSquare ℂ 4).eval (P j)
            (fun i => if i.val = 0 then p.val.val else q.val.val)) ≠ 0,
          Projectivization.mk ℂ
            (fun j => (projectiveSquare ℂ 4).eval (P j)
              (fun i => if i.val = 0 then p.val.val else q.val.val)) h =
            (p + q).val.val := by
  refine ⟨extensionAdditionPolynomials, extensionAdditionPolynomials_homogeneous, ?_⟩
  intro p q hp hq hpq
  have heval : (fun j => (projectiveSquare ℂ 4).eval (extensionAdditionPolynomials j)
          (fun i => if i.val = 0 then p.val.val else q.val.val)) =
      extensionAdditionVector p.val.val.rep q.val.val.rep := by
    ext j
    fin_cases j <;> simp [extensionAdditionPolynomials, extensionAdditionVector,
      MultiProjectiveSpace.eval, MultiProjectiveSpace.coordinate, projectiveSquare]
  have hn := extensionAdditionVector_ne_zero p.val.val.rep q.val.val.rep hp hq hpq
  refine ⟨by simpa only [heval] using hn, ?_⟩
  simpa only [heval] using projective_extension_addition_polynomial L D S hS hS_value η e he p q hn

end WeierstrassEllipticZeta


set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Filter
open scoped Topology
namespace WeierstrassEllipticZeta

/-- Denominator, elliptic numerator, derivative numerator, and zeta numerator
for a translation chart that includes the elliptic identity. The parameter
`half` is specialized to `1/2` in the complex coordinate ring. -/
def extensionOriginData {R : Type*} [CommRing R]
    (g2 g3 a b c half : R) (X : Fin 5 → R) : Fin 4 → R :=
  let D := X 2 ^ 2 + g2 * X 0 * X 1 + g3 * X 0 ^ 2
  let E := D - 4 * a * X 1 ^ 2
  let N := a * D + (4 * a ^ 2 - g2) * X 1 ^ 2 -
    2 * b * X 1 * X 2 - (g2 * a + 2 * g3) * X 0 * X 1
  let A := -6 * X 1 ^ 2 + half * g2 * X 0 ^ 2
  let B := -half * X 2 ^ 2 - g2 * X 0 * X 1 - 3 * half * g3 * X 0 ^ 2
  let Ddot := (g2 * X 1 + 2 * g3 * X 0) * A + g2 * X 0 * B
  let Edot := Ddot - 8 * a * X 1 * B
  let Ndot := a * Ddot + 2 * (4 * a ^ 2 - g2) * X 1 * B -
    2 * b * X 2 * B - (g2 * a + 2 * g3) * (A * X 1 + X 0 * B)
  let F := D * N
  let Y := (Ddot * N + D * Ndot) * E - 2 * F * Edot
  let T := a * D - b * X 1 * X 2 - g2 * X 1 ^ 2 - g3 * X 0 * X 1
  let K := (X 4 + c * X 2) * E + 2 * X 1 * T
  ![E, F, Y, K]

def extensionOriginTranslationVector {R : Type*} [CommRing R]
    (g2 g3 a b c half : R) (X : Fin 5 → R) : Fin 5 → R :=
  let V := extensionOriginData g2 g3 a b c half X
  ![X 2 ^ 2 * V 0 ^ 4, X 2 ^ 2 * V 0 ^ 2 * V 1,
    X 2 * V 0 * V 2, X 2 * V 0 ^ 3 * V 3,
    V 2 * V 3 + 2 * X 2 ^ 2 * V 1 ^ 2]


private theorem extensionOriginData_affine (g2 g3 a b c x y w : ℂ)
    (hy : y ^ 2 - 4 * x ^ 3 + g2 * x + g3 = 0)
    (hb : b ^ 2 - 4 * a ^ 3 + g2 * a + g3 = 0) :
    extensionOriginData g2 g3 a b c (1/2) ![1, x, y, w, y * w + 2 * x ^ 2] =
      let d := x - a
      let t := y - b
      let nx := t ^ 2 - 4 * (x + a) * d ^ 2
      let ny := -4 * y * d ^ 3 + 4 * t * (2 * x + a) * d ^ 2 - t ^ 3
      ![4 * x ^ 2 * d, 4 * x ^ 4 * nx, 16 * y * x ^ 6 * ny,
        2 * x ^ 2 * y * (2 * d * (w + c) + t)] := by
  ext j
  fin_cases j <;> dsimp [extensionOriginData]
  · linear_combination (1) * hy +
      (0) * hb
  · linear_combination (-4 * x ^ 4 + 4 * x ^ 3 * a + 4 * x ^ 2 * a ^ 2 + -1 * x ^ 2 * g2 + -2 * x * y * b + -2 * x * g3 + 1 * y ^ 2 * a + 1 * a * g3) * hy +
      (-4 * x ^ 4) * hb
  · linear_combination (16 * x ^ 6 * y ^ 2 + -32 * x ^ 6 * y * b + -192 * x ^ 6 * a ^ 3 + 48 * x ^ 6 * a * g2 + 48 * x ^ 6 * b ^ 2 + 48 * x ^ 6 * g3 + 48 * x ^ 5 * y * a * b + -48 * x ^ 4 * y ^ 2 * a ^ 2 + 4 * x ^ 4 * y ^ 2 * g2 + -8 * x ^ 4 * y * b * g2 + -24 * x ^ 4 * a ^ 3 * g2 + 6 * x ^ 4 * a * g2 ^ 2 + 4 * x ^ 3 * y ^ 3 * b + -16 * x ^ 3 * y ^ 2 * a ^ 3 + 12 * x ^ 3 * y ^ 2 * a * g2 + 16 * x ^ 3 * y ^ 2 * g3 + 20 * x ^ 3 * y * a * b * g2 + -12 * x ^ 3 * y * b * g3 + -48 * x ^ 3 * a ^ 3 * g3 + -6 * x ^ 3 * a ^ 2 * g2 ^ 2 + 36 * x ^ 3 * a * g2 * g3 + (3 / 2 : ℂ) * x ^ 3 * g2 ^ 3 + 12 * x ^ 2 * y ^ 3 * a * b + -24 * x ^ 2 * y ^ 2 * a ^ 2 * g2 + 12 * x ^ 2 * y ^ 2 * a * g3 + (5 / 2 : ℂ) * x ^ 2 * y ^ 2 * g2 ^ 2 + 36 * x ^ 2 * y * a * b * g3 + 1 * x ^ 2 * y * b * g2 ^ 2 + -36 * x ^ 2 * a ^ 2 * g2 * g3 + 36 * x ^ 2 * a * g3 ^ 2 + (9 / 2 : ℂ) * x ^ 2 * g2 ^ 2 * g3 + -12 * x * y ^ 4 * a ^ 2 + 1 * x * y ^ 4 * g2 + 2 * x * y ^ 3 * b * g2 + -48 * x * y ^ 2 * a ^ 2 * g3 + (1 / 2 : ℂ) * x * y ^ 2 * a * g2 ^ 2 + 5 * x * y ^ 2 * g2 * g3 + 4 * x * y * b * g2 * g3 + -36 * x * a ^ 2 * g3 ^ 2 + (3 / 2 : ℂ) * x * a * g2 ^ 2 * g3 + 6 * x * g2 * g3 ^ 2 + 1 * y ^ 5 * b + (1 / 2 : ℂ) * y ^ 4 * a * g2 + 1 * y ^ 4 * g3 + 4 * y ^ 3 * b * g3 + 2 * y ^ 2 * a * g2 * g3 + 4 * y ^ 2 * g3 ^ 2 + 3 * y * b * g3 ^ 2 + (3 / 2 : ℂ) * a * g2 * g3 ^ 2 + 3 * g3 ^ 3) * hy +
      (192 * x ^ 9 + -48 * x ^ 7 * g2 + -16 * x ^ 6 * y * b + -48 * x ^ 6 * g3) * hb
  · linear_combination (2 * x * a + 1 * y * w + 1 * y * c) * hy +
      (0) * hb

/-- Exact polynomial comparison with the affine addition law. This identity
uses only the two Weierstrass cubic equations. -/
theorem extensionOriginTranslationVector_affine (g2 g3 a b c x y w : ℂ)
    (hy : y ^ 2 - 4 * x ^ 3 + g2 * x + g3 = 0)
    (hb : b ^ 2 - 4 * a ^ 3 + g2 * a + g3 = 0) :
    extensionOriginTranslationVector g2 g3 a b c (1/2)
        ![1, x, y, w, y * w + 2 * x ^ 2] =
      (64 * y ^ 2 * x ^ 8 * (x - a)) •
        extensionAdditionVector ![1, x, y, w, y * w + 2 * x ^ 2]
          ![1, a, b, c, b * c + 2 * a ^ 2] := by
  unfold extensionOriginTranslationVector
  rw [extensionOriginData_affine g2 g3 a b c x y w hy hb]
  ext j
  fin_cases j <;> simp [extensionAdditionVector, Pi.smul_apply, smul_eq_mul] <;> ring

private theorem extensionOriginData_smul
    (g2 g3 a b c half r : ℂ) (X : Fin 5 → ℂ) (j : Fin 4) :
    extensionOriginData g2 g3 a b c half (r • X) j =
      r ^ (![2, 4, 7, 3] j : ℕ) * extensionOriginData g2 g3 a b c half X j := by
  fin_cases j <;> simp [extensionOriginData, Pi.smul_apply, smul_eq_mul] <;> ring

theorem extensionOriginTranslationVector_smul
    (g2 g3 a b c half r : ℂ) (X : Fin 5 → ℂ) :
    extensionOriginTranslationVector g2 g3 a b c half (r • X) =
      r ^ 10 • extensionOriginTranslationVector g2 g3 a b c half X := by
  ext j
  fin_cases j <;> simp [extensionOriginTranslationVector, extensionOriginData_smul,
    Pi.smul_apply, smul_eq_mul] <;> ring

/-- The identity chart has a nonvanishing first coordinate, including every
point in the additive fibre over the elliptic identity. -/
theorem extensionOriginTranslationVector_ne_zero
    (g2 g3 a b c : ℂ) (X : Fin 5 → ℂ)
    (h0 : X 0 = 0) (h1 : X 1 = 0) (h2 : X 2 ≠ 0) :
    extensionOriginTranslationVector g2 g3 a b c (1/2) X ≠ 0 := by
  intro hn
  have hz := congrFun hn 0
  have heq : extensionOriginTranslationVector g2 g3 a b c (1/2) X 0 = X 2 ^ 10 := by
    simp [extensionOriginTranslationVector, extensionOriginData, h0, h1]
    ring
  exact (pow_ne_zero 10 h2) (heq.symm.trans hz)

def extensionOriginPolynomials (g2 g3 a b c : ℂ) : Fin 5 → MvPolynomial (Fin 5) ℂ :=
  extensionOriginTranslationVector (MvPolynomial.C g2) (MvPolynomial.C g3)
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C c) (MvPolynomial.C (1/2))
    MvPolynomial.X

theorem extensionOriginPolynomials_eval (g2 g3 a b c : ℂ) (X : Fin 5 → ℂ) (j : Fin 5) :
    MvPolynomial.eval X (extensionOriginPolynomials g2 g3 a b c j) =
      extensionOriginTranslationVector g2 g3 a b c (1/2) X j := by
  fin_cases j <;> simp [extensionOriginPolynomials, extensionOriginTranslationVector, extensionOriginData]

/-- The chart near the elliptic identity represents the same translated entire
curve as the affine addition law, also at lattice parameters. -/
theorem entire_extension_origin_translation_cross_products
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (v : ℂ) (hv : v ∉ L.lattice) (z u t : ℂ) (i j : Fin 5) :
    let R := extensionOriginTranslationVector L.g₂ L.g₃ (L.weierstrassP v)
      (L.derivWeierstrassP v) (weierstrassZeta L v + t) (1/2)
    R (entireExtensionVector S z u) i * entireExtensionVector S (z + v) (u + t) j =
      R (entireExtensionVector S z u) j * entireExtensionVector S (z + v) (u + t) i := by
  dsimp only
  let R := extensionOriginTranslationVector L.g₂ L.g₃ (L.weierstrassP v)
    (L.derivWeierstrassP v) (weierstrassZeta L v + t) (1/2)
  let B (z : ℂ) := entireExtensionVector S (z + v) (u + t)
  have hσ (z : ℂ) (hz : z ∉ L.lattice) : D.sigma z ≠ 0 := by
    intro hzero
    obtain ⟨k, hk⟩ := hS_ne z
    exact hk (by simp [hS_value z hz k, hzero])
  have hSV (u : ℂ) (k : Fin 5) (w : ℂ) :
      AnalyticAt ℂ (fun x => entireExtensionVector S x u k) w := by
    have hs (k : Fin 5) := hS k w (Set.mem_univ w)
    fin_cases k <;> dsimp [entireExtensionVector] <;> fun_prop
  have hR (k : Fin 5) : AnalyticOnNhd ℂ (fun z => R (entireExtensionVector S z u) k) Set.univ := by
    intro w _
    have ha := AnalyticAt.aeval_mvPolynomial (fun k => hSV u k w)
      (extensionOriginPolynomials L.g₂ L.g₃ (L.weierstrassP v) (L.derivWeierstrassP v)
        (weierstrassZeta L v + t) k)
    simpa only [MvPolynomial.aeval_eq_eval, extensionOriginPolynomials_eval] using ha
  have hB (k : Fin 5) : AnalyticOnNhd ℂ (fun z => B z k) Set.univ := by
    intro w _
    exact (hSV (u + t) k (w + v)).comp (f := fun x : ℂ => x + v) (x := w)
      (analyticAt_id.add analyticAt_const)
  have hreg (z : ℂ) (hz : z ∉ L.lattice) :
      R (entireExtensionVector S z u) i * B z j =
        R (entireExtensionVector S z u) j * B z i := by
    have hy : L.derivWeierstrassP z ^ 2 - 4 * L.weierstrassP z ^ 3 +
        L.g₂ * L.weierstrassP z + L.g₃ = 0 := by
      linear_combination L.derivWeierstrassP_sq z hz
    have hb : L.derivWeierstrassP v ^ 2 - 4 * L.weierstrassP v ^ 3 +
        L.g₂ * L.weierstrassP v + L.g₃ = 0 := by
      linear_combination L.derivWeierstrassP_sq v hv
    have hc := entire_extension_addition_cross_products L D S hS hS_value z v u t i j
    rw [entireExtensionVector_value L D S hS_value z u hz,
      entireExtensionVector_value L D S hS_value v t hv,
      extensionAdditionVector_smul] at hc
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc] at hc
    have hcoef : (D.sigma z ^ 3) ^ 5 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (hσ z hz))
    have hcoef' : (D.sigma v ^ 3) ^ 5 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (hσ v hv))
    have heq := mul_left_cancel₀ hcoef' (mul_left_cancel₀ hcoef hc)
    change R (entireExtensionVector S z u) i * B z j = _
    dsimp only [R]
    rw [entireExtensionVector_value L D S hS_value z u hz,
      extensionOriginTranslationVector_smul, extensionOriginTranslationVector_affine
        L.g₂ L.g₃ (L.weierstrassP v) (L.derivWeierstrassP v) (weierstrassZeta L v + t)
        (L.weierstrassP z) (L.derivWeierstrassP z) (weierstrassZeta L z + u) hy hb]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    have hh := congrArg (fun r => (D.sigma z ^ 3) ^ 10 *
      (64 * L.derivWeierstrassP z ^ 2 * L.weierstrassP z ^ 8 *
        (L.weierstrassP z - L.weierstrassP v) * r)) heq
    simpa only [mul_assoc] using hh
  have heq : (fun z => R (entireExtensionVector S z u) i * B z j) =
      (fun z => R (entireExtensionVector S z u) j * B z i) := by
    apply AnalyticOnNhd.eq_of_eventuallyEq ((hR i).mul (hB j)) ((hR j).mul (hB i))
      (z₀ := L.ω₁ / 2)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds
      L.ω₁_div_two_notMem_lattice] with z hz
    exact hreg z hz
  exact congrFun heq z


theorem extensionOriginPolynomials_homogeneous (g2 g3 a b c : ℂ) :
    ∀ j, (extensionOriginPolynomials g2 g3 a b c j).IsHomogeneous 10 := by
  let X : Fin 5 → MvPolynomial (Fin 5) ℂ := MvPolynomial.X
  let g2' := MvPolynomial.C g2 (σ := Fin 5)
  let g3' := MvPolynomial.C g3 (σ := Fin 5)
  let a' := MvPolynomial.C a (σ := Fin 5)
  let b' := MvPolynomial.C b (σ := Fin 5)
  let c' := MvPolynomial.C c (σ := Fin 5)
  let half' := MvPolynomial.C (1/2 : ℂ) (σ := Fin 5)
  let D := X 2 ^ 2 + g2' * X 0 * X 1 + g3' * X 0 ^ 2
  let E := D - 4 * a' * X 1 ^ 2
  let N := a' * D + (4 * a' ^ 2 - g2') * X 1 ^ 2 -
    2 * b' * X 1 * X 2 - (g2' * a' + 2 * g3') * X 0 * X 1
  let A := -6 * X 1 ^ 2 + half' * g2' * X 0 ^ 2
  let B := -half' * X 2 ^ 2 - g2' * X 0 * X 1 - 3 * half' * g3' * X 0 ^ 2
  let Ddot := (g2' * X 1 + 2 * g3' * X 0) * A + g2' * X 0 * B
  let Edot := Ddot - 8 * a' * X 1 * B
  let Ndot := a' * Ddot + 2 * (4 * a' ^ 2 - g2') * X 1 * B -
    2 * b' * X 2 * B - (g2' * a' + 2 * g3') * (A * X 1 + X 0 * B)
  let F := D * N
  let Y := (Ddot * N + D * Ndot) * E - 2 * F * Edot
  let T := a' * D - b' * X 1 * X 2 - g2' * X 1 ^ 2 - g3' * X 0 * X 1
  let K := (X 4 + c' * X 2) * E + 2 * X 1 * T
  have hX (j : Fin 5) : (X j).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X ℂ j
  have hc (r : ℂ) : (MvPolynomial.C r (σ := Fin 5)).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C _ r
  have hn (n : ℕ) : (n : MvPolynomial (Fin 5) ℂ).IsHomogeneous 0 := by
    simpa only [map_natCast] using hc (n : ℂ)
  have hD : D.IsHomogeneous 2 := ((hX 2).pow 2).add
    (((hc g2).mul (hX 0)).mul (hX 1)) |>.add ((hc g3).mul ((hX 0).pow 2))
  have hE : E.IsHomogeneous 2 := hD.sub (((hn 4).mul (hc a)).mul ((hX 1).pow 2))
  have hcoeff : (4 * a' ^ 2 - g2').IsHomogeneous 0 := ((hn 4).mul ((hc a).pow 2)).sub (hc g2)
  have hcoeff' : (g2' * a' + 2 * g3').IsHomogeneous 0 :=
    ((hc g2).mul (hc a)).add ((hn 2).mul (hc g3))
  have hN : N.IsHomogeneous 2 := (((hc a).mul hD).add (hcoeff.mul ((hX 1).pow 2)) |>.sub
    ((((hn 2).mul (hc b)).mul (hX 1)).mul (hX 2))) |>.sub
    ((hcoeff'.mul (hX 0)).mul (hX 1))
  have hA : A.IsHomogeneous 2 := (((hn 6).neg).mul ((hX 1).pow 2)).add
    (((hc (1/2)).mul (hc g2)).mul ((hX 0).pow 2))
  have hB : B.IsHomogeneous 2 := ((((hc (1/2)).neg).mul ((hX 2).pow 2)).sub
    (((hc g2).mul (hX 0)).mul (hX 1))) |>.sub
    ((((hn 3).mul (hc (1/2))).mul (hc g3)).mul ((hX 0).pow 2))
  have hDd : Ddot.IsHomogeneous 3 :=
    ((((hc g2).mul (hX 1)).add (((hn 2).mul (hc g3)).mul (hX 0))).mul hA).add
      (((hc g2).mul (hX 0)).mul hB)
  have hEd : Edot.IsHomogeneous 3 := hDd.sub ((((hn 8).mul (hc a)).mul (hX 1)).mul hB)
  have hNd : Ndot.IsHomogeneous 3 := (((hc a).mul hDd).add
    ((((hn 2).mul hcoeff).mul (hX 1)).mul hB) |>.sub
    ((((hn 2).mul (hc b)).mul (hX 2)).mul hB)) |>.sub
    (hcoeff'.mul ((hA.mul (hX 1)).add ((hX 0).mul hB)))
  have hF : F.IsHomogeneous 4 := hD.mul hN
  have hY : Y.IsHomogeneous 7 := (((hDd.mul hN).add (hD.mul hNd)).mul hE).sub
    (((hn 2).mul hF).mul hEd)
  have hT : T.IsHomogeneous 2 := (((hc a).mul hD).sub
    (((hc b).mul (hX 1)).mul (hX 2)) |>.sub ((hc g2).mul ((hX 1).pow 2))) |>.sub
    (((hc g3).mul (hX 0)).mul (hX 1))
  have hK : K.IsHomogeneous 3 := (((hX 4).add ((hc c).mul (hX 2))).mul hE).add
    (((hn 2).mul (hX 1)).mul hT)
  intro j
  fin_cases j
  · exact ((hX 2).pow 2).mul (hE.pow 4)
  · exact (((hX 2).pow 2).mul (hE.pow 2)).mul hF
  · exact ((hX 2).mul hE).mul hY
  · exact ((hX 2).mul (hE.pow 3)).mul hK
  · exact (hY.mul hK).add ((((hn 2).mul ((hX 2).pow 2)).mul (hF.pow 2)))

end WeierstrassEllipticZeta


set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open TranscendenceTheory
namespace WeierstrassEllipticZeta

/-- Homogeneous translation formulas valid near the entire additive fibre above
 the elliptic identity, with correctness on their whole nonvanishing locus. -/
theorem projective_extension_origin_translation_law
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)

    (v t : ℂ) (hv : v ∉ L.lattice) :
    ∃ P : Fin 5 → MvPolynomial (Fin 5) ℂ,
      (∀ j, (P j).IsHomogeneous 10) ∧
      (∀ (p : ProjectiveExtensionChartLocus L.g₂ L.g₃)
          (hn : (fun j => MvPolynomial.eval p.val.val.rep (P j)) ≠ 0),
        Projectivization.mk ℂ (fun j => MvPolynomial.eval p.val.val.rep (P j)) hn =
          (p + e ((extensionPeriodGraph L.lattice η).mkQ (v, t))).val.val) ∧
      (∀ p : ProjectiveExtensionChartLocus L.g₂ L.g₃,
        p.val.val.rep 0 = 0 → (fun j => MvPolynomial.eval p.val.val.rep (P j)) ≠ 0) := by
  let P := extensionOriginPolynomials L.g₂ L.g₃ (L.weierstrassP v)
    (L.derivWeierstrassP v) (weierstrassZeta L v + t)
  have hev (X : Fin 5 → ℂ) : (fun j => MvPolynomial.eval X (P j)) =
      extensionOriginTranslationVector L.g₂ L.g₃ (L.weierstrassP v)
        (L.derivWeierstrassP v) (weierstrassZeta L v + t) (1/2) X := by
    ext j
    exact extensionOriginPolynomials_eval _ _ _ _ _ _ _
  refine ⟨P, extensionOriginPolynomials_homogeneous _ _ _ _ _, ?_, ?_⟩
  · intro p hn
    obtain ⟨p, rfl⟩ := e.surjective p
    obtain ⟨⟨z, u⟩, rfl⟩ := (extensionPeriodGraph L.lattice η).mkQ_surjective p
    obtain ⟨hX, hPX⟩ := he z u
    obtain ⟨hB, hPB⟩ := he (z + v) (u + t)
    have hsum : e ((extensionPeriodGraph L.lattice η).mkQ (z + v, u + t)) =
        e ((extensionPeriodGraph L.lattice η).mkQ (z, u)) +
          e ((extensionPeriodGraph L.lattice η).mkQ (v, t)) := by
      change e ((extensionPeriodGraph L.lattice η).mkQ ((z, u) + (v, t))) = _
      rw [map_add, map_add]
    rw [hsum] at hPB
    rw [hPB]
    apply projective_eq_of_cross_products _ _ hn hB
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ _ hX
    simp only [P, extensionOriginPolynomials_eval]
    rw [hPX, ← ha]
    simp only [Units.smul_def, extensionOriginTranslationVector_smul,
      Pi.smul_apply, smul_eq_mul]
    intro i j
    have hc := entire_extension_origin_translation_cross_products L D S hS hS_value hS_ne
      v hv z u t i j
    dsimp only [entireExtensionVector] at hc
    have hh := congrArg (fun r => a.val ^ 10 * r) hc
    simpa only [mul_assoc] using hh
  · intro p h0
    have h1 : p.val.val.rep 1 = 0 := by
      have hc := p.val.property.2
      simpa [extensionCubic, h0] using hc
    have h2 : p.val.val.rep 2 ≠ 0 := by
      rcases p.property with h | h
      · exact False.elim (h h0)
      · exact h
    rw [hev]
    exact extensionOriginTranslationVector_ne_zero _ _ _ _ _ _ h0 h1 h2

end WeierstrassEllipticZeta



set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace PhilipponMultiplicity
universe u
open scoped BigOperators

theorem block_isHomogeneous {K : Type u} [Field K] (M : MultiProjectiveSpace K)
    (b : M.FactorIndex) {d : ℕ}
    {P : MvPolynomial (Fin (M.ambientDimension b + 1)) K} (hP : P.IsHomogeneous d) :
    M.IsHomogeneous (MvPolynomial.rename (fun j => ⟨b, j⟩) P)
      (fun i => if i = b then d else 0) := by
  classical
  let f : Fin (M.ambientDimension b + 1) → M.Variable := fun j => ⟨b, j⟩
  have hf : Function.Injective f := fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h |>.2)
  intro a ha i
  rw [MvPolynomial.support_rename_of_injective hf] at ha
  obtain ⟨m, hm, hma⟩ := Finset.mem_image.mp ha
  subst a
  by_cases hi : i = b
  · subst i
    change (∑ j, (m.mapDomain f) (f j)) = if b = b then d else 0
    simp only [if_pos rfl, Finsupp.mapDomain_apply hf]
    have hh := hP (MvPolynomial.mem_support_iff.mp hm)
    change Finsupp.weight (1 : Fin (M.ambientDimension b + 1) → ℕ) m = d at hh
    simpa [Finsupp.weight_eq_sum] using hh
  · simp only [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨k, hk⟩
    exact hi (congrArg Sigma.fst hk).symm

theorem multiprojective_regular_of_local_homogeneous
    {K X : Type u} [Field K] (M : MultiProjectiveSpace K) {N' : ℕ}
    (e : X → M.Point) (f : X → Projectivization K (Fin (N' + 1) → K))
    (hf : ∀ x : X, ∃ D : M.FactorIndex → ℕ,
      ∃ P : Fin (N' + 1) → M.CoordinateRing,
        (∀ j, M.IsHomogeneous (P j) D) ∧
        (fun j => M.eval (P j) (e x)) ≠ 0 ∧
        ∀ y : X, ∀ hn : (fun j => M.eval (P j) (e y)) ≠ 0,
          Projectivization.mk K (fun j => M.eval (P j) (e y)) hn = f y) :
    M.IsRegularAlong (projectiveSpace K N') e (fun x => fun _ => f x) := by
  classical
  intro x b
  obtain ⟨D, P, hP, hn, hcorrect⟩ := hf x
  obtain ⟨j, hj⟩ : ∃ j, M.eval (P j) (e x) ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  refine ⟨{p | M.eval (P j) p ≠ 0}, M.isOpen_basic _ _ (hP j), hj,
    D, P, hP, ?_⟩
  intro y hy
  have hny : (fun k => M.eval (P k) (e y)) ≠ 0 := by
    intro h
    exact hy (congrFun h j)
  exact ⟨hny, hcorrect y hny⟩

/-- A homogeneous tuple around each source point suffices. Its nonvanishing
coordinate supplies the required ambient Zariski-open neighborhood. -/
theorem projective_regular_of_local_homogeneous
    {K X : Type u} [Field K] {N N' : ℕ}
    (e : X → Projectivization K (Fin (N + 1) → K))
    (f : X → Projectivization K (Fin (N' + 1) → K))
    (hf : ∀ x : X, ∃ d : ℕ, ∃ P : Fin (N' + 1) → MvPolynomial (Fin (N + 1)) K,
      (∀ j, (P j).IsHomogeneous d) ∧
      (fun j => MvPolynomial.eval (e x).rep (P j)) ≠ 0 ∧
      ∀ y : X, ∀ hn : (fun j => MvPolynomial.eval (e y).rep (P j)) ≠ 0,
        Projectivization.mk K (fun j => MvPolynomial.eval (e y).rep (P j)) hn = f y) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace K N) (projectiveSpace K N')
      (fun x => fun _ => e x) (fun x => fun _ => f x) := by
  classical
  letI := (projectiveSpace K N).zariskiTopology
  intro x b
  obtain ⟨d, P, hP, hn, hcorrect⟩ := hf x
  obtain ⟨j, hj⟩ : ∃ j, MvPolynomial.eval (e x).rep (P j) ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  let Q : Fin (N' + 1) → (projectiveSpace K N).CoordinateRing :=
    fun j => MvPolynomial.rename (fun k => ⟨(0 : Fin 1), k⟩) (P j)
  have heval (y : X) (j : Fin (N' + 1)) :
      (projectiveSpace K N).eval (Q j) (fun _ => e y) =
        MvPolynomial.eval (e y).rep (P j) := by
    simp only [Q, MultiProjectiveSpace.eval, MvPolynomial.eval_rename]
    rfl
  refine ⟨{p | (projectiveSpace K N).eval (Q j) p ≠ 0},
    (projectiveSpace K N).isOpen_basic _ _ (singleBlock_isHomogeneous (hP j)),
    ?_, fun _ => d, Q, (fun k => singleBlock_isHomogeneous (hP k)), ?_⟩
  · change (projectiveSpace K N).eval (Q j) (fun _ => e x) ≠ 0
    simpa only [heval] using hj
  · intro y hy
    have hny : (fun k => MvPolynomial.eval (e y).rep (P k)) ≠ 0 := by
      intro h
      apply hy
      rw [heval y j]
      exact congrFun h j
    have heq : (fun k => (projectiveSpace K N).eval (Q k) (fun _ => e y)) =
        (fun k => MvPolynomial.eval (e y).rep (P k)) := funext (heval y)
    change ∃ hn : (fun k : Fin (N' + 1) =>
        (projectiveSpace K N).eval (Q k) (fun _ => e y)) ≠ 0,
      Projectivization.mk K (fun k : Fin (N' + 1) =>
        (projectiveSpace K N).eval (Q k) (fun _ => e y)) hn = f y
    refine ⟨by simpa only [heq] using hny, ?_⟩
    simpa only [heq] using hcorrect y hny

end PhilipponMultiplicity


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
noncomputable section
open Filter
open scoped Topology
namespace WeierstrassEllipticZeta

/-- The second affine slope chart, including equal base points with nonzero
elliptic derivative. -/
def extensionTangentData {R : Type*} [CommRing R]
    (g2 a b c : R) (X : Fin 5 → R) : Fin 5 → R :=
  let U := 2 * (X 2 + b * X 0)
  let H := 4 * (X 1 ^ 2 + a * X 1 * X 0 + a ^ 2 * X 0 ^ 2) - g2 * X 0 ^ 2
  let N := H ^ 2 - (X 1 + a * X 0) * X 0 * U ^ 2
  let J := -X 2 * X 0 ^ 2 * U ^ 3 + 2 * H * (X 1 * X 0 * U ^ 2 - N)
  let K := (X 3 + c * X 0) * U + H
  ![U, H, N, J, K]

def extensionTangentTranslationVector {R : Type*} [CommRing R]
    (g2 a b c : R) (X : Fin 5 → R) : Fin 5 → R :=
  let V := extensionTangentData g2 a b c X
  ![X 0 ^ 4 * V 0 ^ 4, X 0 ^ 2 * V 0 ^ 2 * V 2,
    X 0 * V 0 * V 3, X 0 ^ 3 * V 0 ^ 3 * V 4,
    V 3 * V 4 + 2 * V 2 ^ 2]

theorem extensionTangentTranslationVector_affine (g2 g3 a b c x y w : ℂ)
    (hy : y ^ 2 - 4 * x ^ 3 + g2 * x + g3 = 0)
    (hb : b ^ 2 - 4 * a ^ 3 + g2 * a + g3 = 0)
    (hd : x - a ≠ 0) :
    (4 * (x - a) ^ 3) • extensionTangentTranslationVector g2 a b c
        ![1, x, y, w, y * w + 2 * x ^ 2] =
      (2 * (y + b)) ^ 4 •
        extensionAdditionVector ![1, x, y, w, y * w + 2 * x ^ 2]
          ![1, a, b, c, b * c + 2 * a ^ 2] := by
  have hH : 4 * (x ^ 2 + a * x + a ^ 2) - g2 =
      (2 * (y + b)) * (y - b) / (2 * (x - a)) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hd)).mpr
    linear_combination -2 * hy + 2 * hb
  ext j
  fin_cases j <;>
    simp [extensionTangentTranslationVector, extensionTangentData,
      extensionAdditionVector, Pi.smul_apply, smul_eq_mul, hH] <;>
    field_simp <;> ring

private theorem extensionTangentData_smul (g2 a b c r : ℂ) (X : Fin 5 → ℂ)
    (j : Fin 5) :
    extensionTangentData g2 a b c (r • X) j =
      r ^ (![1, 2, 4, 6, 2] j : ℕ) * extensionTangentData g2 a b c X j := by
  fin_cases j <;> simp [extensionTangentData, Pi.smul_apply, smul_eq_mul] <;> ring

theorem extensionTangentTranslationVector_smul (g2 a b c r : ℂ) (X : Fin 5 → ℂ) :
    extensionTangentTranslationVector g2 a b c (r • X) =
      r ^ 8 • extensionTangentTranslationVector g2 a b c X := by
  ext j
  fin_cases j <;> simp [extensionTangentTranslationVector, extensionTangentData_smul,
    Pi.smul_apply, smul_eq_mul] <;> ring

theorem extensionTangentTranslationVector_ne_zero (g2 a b c : ℂ) (X : Fin 5 → ℂ)
    (h0 : X 0 ≠ 0) (h2 : X 2 + b * X 0 ≠ 0) :
    extensionTangentTranslationVector g2 a b c X ≠ 0 := by
  intro hn
  have hz := congrFun hn 0
  exact (mul_ne_zero (pow_ne_zero 4 h0)
    (pow_ne_zero 4 (mul_ne_zero (by norm_num) h2))) hz

def extensionTangentPolynomials (g2 a b c : ℂ) : Fin 5 → MvPolynomial (Fin 5) ℂ :=
  extensionTangentTranslationVector (MvPolynomial.C g2) (MvPolynomial.C a)
    (MvPolynomial.C b) (MvPolynomial.C c) MvPolynomial.X

theorem extensionTangentPolynomials_eval (g2 a b c : ℂ) (X : Fin 5 → ℂ) (j : Fin 5) :
    MvPolynomial.eval X (extensionTangentPolynomials g2 a b c j) =
      extensionTangentTranslationVector g2 a b c X j := by
  fin_cases j <;> simp [extensionTangentPolynomials, extensionTangentTranslationVector,
    extensionTangentData]

theorem extensionTangentPolynomials_homogeneous (g2 a b c : ℂ) :
    ∀ j, (extensionTangentPolynomials g2 a b c j).IsHomogeneous 8 := by
  let X : Fin 5 → MvPolynomial (Fin 5) ℂ := MvPolynomial.X
  let g2' := MvPolynomial.C g2 (σ := Fin 5)
  let a' := MvPolynomial.C a (σ := Fin 5)
  let b' := MvPolynomial.C b (σ := Fin 5)
  let c' := MvPolynomial.C c (σ := Fin 5)
  let U := 2 * (X 2 + b' * X 0)
  let H := 4 * (X 1 ^ 2 + a' * X 1 * X 0 + a' ^ 2 * X 0 ^ 2) - g2' * X 0 ^ 2
  let N := H ^ 2 - (X 1 + a' * X 0) * X 0 * U ^ 2
  let J := -X 2 * X 0 ^ 2 * U ^ 3 + 2 * H * (X 1 * X 0 * U ^ 2 - N)
  let K := (X 3 + c' * X 0) * U + H
  have hX (j : Fin 5) : (X j).IsHomogeneous 1 := MvPolynomial.isHomogeneous_X ℂ j
  have hc (r : ℂ) : (MvPolynomial.C r (σ := Fin 5)).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C _ r
  have hn (n : ℕ) : (n : MvPolynomial (Fin 5) ℂ).IsHomogeneous 0 := by
    simpa using hc n
  have hU : U.IsHomogeneous 1 := (hn 2).mul ((hX 2).add ((hc b).mul (hX 0)))
  have hH : H.IsHomogeneous 2 := ((hn 4).mul
    ((((hX 1).pow 2).add (((hc a).mul (hX 1)).mul (hX 0))).add
      (((hc a).pow 2).mul ((hX 0).pow 2)))).sub ((hc g2).mul ((hX 0).pow 2))
  have hN : N.IsHomogeneous 4 := (hH.pow 2).sub
    ((((hX 1).add ((hc a).mul (hX 0))).mul (hX 0)).mul (hU.pow 2))
  have hJ : J.IsHomogeneous 6 := ((((hX 2).neg).mul ((hX 0).pow 2)).mul
    (hU.pow 3)).add (((hn 2).mul hH).mul
      ((((hX 1).mul (hX 0)).mul (hU.pow 2)).sub hN))
  have hK : K.IsHomogeneous 2 := (((hX 3).add ((hc c).mul (hX 0))).mul hU).add hH
  intro j
  change (extensionTangentTranslationVector g2' a' b' c' X j).IsHomogeneous 8
  fin_cases j
  · exact ((hX 0).pow 4).mul (hU.pow 4)
  · exact (((hX 0).pow 2).mul (hU.pow 2)).mul hN
  · exact ((hX 0).mul hU).mul hJ
  · exact (((hX 0).pow 3).mul (hU.pow 3)).mul hK
  · exact (hJ.mul hK).add ((hn 2).mul (hN.pow 2))

/-- The equal-base-point chart agrees with the actual translated entire curve,
including at lattice parameters, by analytic continuation. -/
theorem entire_extension_tangent_translation_cross_products
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (v : ℂ) (hv : v ∉ L.lattice) (z u t : ℂ) (i j : Fin 5) :
    let R := extensionTangentTranslationVector L.g₂ (L.weierstrassP v)
      (L.derivWeierstrassP v) (weierstrassZeta L v + t)
    R (entireExtensionVector S z u) i * entireExtensionVector S (z + v) (u + t) j =
      R (entireExtensionVector S z u) j * entireExtensionVector S (z + v) (u + t) i := by
  dsimp only
  let R := extensionTangentTranslationVector L.g₂ (L.weierstrassP v)
    (L.derivWeierstrassP v) (weierstrassZeta L v + t)
  let B (z : ℂ) := entireExtensionVector S (z + v) (u + t)
  have hσ (z : ℂ) (hz : z ∉ L.lattice) : D.sigma z ≠ 0 := by
    intro hzero
    obtain ⟨k, hk⟩ := hS_ne z
    exact hk (by simp [hS_value z hz k, hzero])
  have hSV (u : ℂ) (k : Fin 5) (w : ℂ) :
      AnalyticAt ℂ (fun x => entireExtensionVector S x u k) w := by
    have hs (k : Fin 5) := hS k w (Set.mem_univ w)
    fin_cases k <;> dsimp [entireExtensionVector] <;> fun_prop
  have hR (k : Fin 5) : AnalyticOnNhd ℂ (fun z => R (entireExtensionVector S z u) k) Set.univ := by
    intro w _
    have ha := AnalyticAt.aeval_mvPolynomial (fun k => hSV u k w)
      (extensionTangentPolynomials L.g₂ (L.weierstrassP v) (L.derivWeierstrassP v)
        (weierstrassZeta L v + t) k)
    simpa only [MvPolynomial.aeval_eq_eval, extensionTangentPolynomials_eval] using ha
  have hB (k : Fin 5) : AnalyticOnNhd ℂ (fun z => B z k) Set.univ := by
    intro w _
    exact (hSV (u + t) k (w + v)).comp (f := fun x : ℂ => x + v) (x := w)
      (analyticAt_id.add analyticAt_const)
  have hreg (z : ℂ) (hz : z ∉ L.lattice)
      (hd : L.weierstrassP z - L.weierstrassP v ≠ 0) :
      R (entireExtensionVector S z u) i * B z j =
        R (entireExtensionVector S z u) j * B z i := by
    have hy : L.derivWeierstrassP z ^ 2 - 4 * L.weierstrassP z ^ 3 +
        L.g₂ * L.weierstrassP z + L.g₃ = 0 := by
      linear_combination L.derivWeierstrassP_sq z hz
    have hb : L.derivWeierstrassP v ^ 2 - 4 * L.weierstrassP v ^ 3 +
        L.g₂ * L.weierstrassP v + L.g₃ = 0 := by
      linear_combination L.derivWeierstrassP_sq v hv
    have hc := entire_extension_addition_cross_products L D S hS hS_value z v u t i j
    rw [entireExtensionVector_value L D S hS_value z u hz,
      entireExtensionVector_value L D S hS_value v t hv,
      extensionAdditionVector_smul] at hc
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc] at hc
    have hcoef : (D.sigma z ^ 3) ^ 5 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (hσ z hz))
    have hcoef' : (D.sigma v ^ 3) ^ 5 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (hσ v hv))
    have heq := mul_left_cancel₀ hcoef' (mul_left_cancel₀ hcoef hc)
    have hcmp := extensionTangentTranslationVector_affine L.g₂ L.g₃
      (L.weierstrassP v) (L.derivWeierstrassP v) (weierstrassZeta L v + t)
      (L.weierstrassP z) (L.derivWeierstrassP z) (weierstrassZeta L z + u) hy hb hd
    have hci := congrFun hcmp i
    have hcj := congrFun hcmp j
    simp only [Pi.smul_apply, smul_eq_mul] at hci hcj
    have hnorm :
        R ![1, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z + u,
          L.derivWeierstrassP z * (weierstrassZeta L z + u) + 2 * L.weierstrassP z ^ 2] i * B z j =
        R ![1, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z + u,
          L.derivWeierstrassP z * (weierstrassZeta L z + u) + 2 * L.weierstrassP z ^ 2] j * B z i := by
      apply mul_left_cancel₀ (mul_ne_zero (show (4 : ℂ) ≠ 0 by norm_num) (pow_ne_zero 3 hd))
      change 4 * (L.weierstrassP z - L.weierstrassP v) ^ 3 * _ = _
      linear_combination B z j * hci - B z i * hcj +
        (2 * (L.derivWeierstrassP z + L.derivWeierstrassP v)) ^ 4 * heq
    dsimp only [R]
    rw [entireExtensionVector_value L D S hS_value z u hz,
      extensionTangentTranslationVector_smul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact congrArg (fun r => (D.sigma z ^ 3) ^ 8 * r) hnorm
  have ha := L.ω₁_div_two_notMem_lattice
  have hnear0 : ∀ᶠ z in 𝓝 (L.ω₁ / 2), z ∉ L.lattice :=
    L.isClosed_lattice.isOpen_compl.mem_nhds ha
  have hnear : ∀ᶠ z in 𝓝[≠] (L.ω₁ / 2), z ∉ L.lattice :=
    hnear0.filter_mono nhdsWithin_le_nhds
  obtain ⟨a, ha, had⟩ := (hnear.and
    (weierstrassP_eventually_ne L (L.ω₁ / 2) (L.weierstrassP v) ha)).exists
  have heq : (fun z => R (entireExtensionVector S z u) i * B z j) =
      (fun z => R (entireExtensionVector S z u) j * B z i) := by
    apply AnalyticOnNhd.eq_of_eventuallyEq ((hR i).mul (hB j)) ((hR j).mul (hB i))
      (z₀ := a)
    have hcont := ((L.analyticOnNhd_weierstrassP a ha).continuousAt.sub
      continuousAt_const).eventually_ne (sub_ne_zero.mpr had)
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds ha, hcont] with z hz hd
    exact hreg z hz hd
  exact congrFun heq z

end WeierstrassEllipticZeta


set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open TranscendenceTheory
namespace WeierstrassEllipticZeta

/-- The second affine slope chart represents translation on its entire nonvanishing locus. -/
theorem projective_extension_tangent_translation_law
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)

    (v t : ℂ) (hv : v ∉ L.lattice) :
    ∃ P : Fin 5 → MvPolynomial (Fin 5) ℂ,
      (∀ j, (P j).IsHomogeneous 8) ∧
      (∀ (p : ProjectiveExtensionChartLocus L.g₂ L.g₃)
          (hn : (fun j => MvPolynomial.eval p.val.val.rep (P j)) ≠ 0),
        Projectivization.mk ℂ (fun j => MvPolynomial.eval p.val.val.rep (P j)) hn =
          (p + e ((extensionPeriodGraph L.lattice η).mkQ (v, t))).val.val) ∧
      (∀ p : ProjectiveExtensionChartLocus L.g₂ L.g₃,
        p.val.val.rep 0 ≠ 0 →
        p.val.val.rep 2 + L.derivWeierstrassP v * p.val.val.rep 0 ≠ 0 →
        (fun j => MvPolynomial.eval p.val.val.rep (P j)) ≠ 0) := by
  let P := extensionTangentPolynomials L.g₂ (L.weierstrassP v)
    (L.derivWeierstrassP v) (weierstrassZeta L v + t)
  have hev (X : Fin 5 → ℂ) : (fun j => MvPolynomial.eval X (P j)) =
      extensionTangentTranslationVector L.g₂ (L.weierstrassP v)
        (L.derivWeierstrassP v) (weierstrassZeta L v + t) X := by
    ext j
    exact extensionTangentPolynomials_eval _ _ _ _ _ _
  refine ⟨P, extensionTangentPolynomials_homogeneous _ _ _ _, ?_, ?_⟩
  · intro p hn
    obtain ⟨p, rfl⟩ := e.surjective p
    obtain ⟨⟨z, u⟩, rfl⟩ := (extensionPeriodGraph L.lattice η).mkQ_surjective p
    obtain ⟨hX, hPX⟩ := he z u
    obtain ⟨hB, hPB⟩ := he (z + v) (u + t)
    have hsum : e ((extensionPeriodGraph L.lattice η).mkQ (z + v, u + t)) =
        e ((extensionPeriodGraph L.lattice η).mkQ (z, u)) +
          e ((extensionPeriodGraph L.lattice η).mkQ (v, t)) := by
      change e ((extensionPeriodGraph L.lattice η).mkQ ((z, u) + (v, t))) = _
      rw [map_add, map_add]
    rw [hsum] at hPB
    rw [hPB]
    apply projective_eq_of_cross_products _ _ hn hB
    obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ _ hX
    simp only [P, extensionTangentPolynomials_eval]
    rw [hPX, ← ha]
    simp only [Units.smul_def, extensionTangentTranslationVector_smul,
      Pi.smul_apply, smul_eq_mul]
    intro i j
    have hc := entire_extension_tangent_translation_cross_products L D S hS hS_value hS_ne
      v hv z u t i j
    dsimp only [entireExtensionVector] at hc
    have hh := congrArg (fun r => a.val ^ 8 * r) hc
    simpa only [mul_assoc] using hh
  · intro p h0 h2
    rw [hev]
    exact extensionTangentTranslationVector_ne_zero _ _ _ _ _ h0 h2

end WeierstrassEllipticZeta



set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open TranscendenceTheory PhilipponMultiplicity
namespace WeierstrassEllipticZeta

private theorem _root_.MvPolynomial.IsHomogeneous.mulConstant {P : MvPolynomial (Fin 5) ℂ}
    {d : ℕ} (h : P.IsHomogeneous d) (n : ℕ) : (n * P).IsHomogeneous d := by
  simpa using (MvPolynomial.isHomogeneous_C (Fin 5) (n : ℂ)).mul h

private def extensionAffineTranslationPolynomials (Y : Fin 5 → ℂ) :
    Fin 5 → MvPolynomial (Fin 5) ℂ :=
  extensionAdditionVector MvPolynomial.X (fun j => MvPolynomial.C (Y j))

private theorem extensionAffineTranslationPolynomials_homogeneous (V : Fin 5 → ℂ) :
    ∀ j, (extensionAffineTranslationPolynomials V j).IsHomogeneous 5 := by
  let X : Fin 5 → MvPolynomial (Fin 5) ℂ := MvPolynomial.X
  let Y : Fin 5 → MvPolynomial (Fin 5) ℂ := fun j => MvPolynomial.C (V j)
  have hXY (a b : Fin 5) : (X a * Y b).IsHomogeneous 1 :=
    (MvPolynomial.isHomogeneous_X ℂ a).mul (MvPolynomial.isHomogeneous_C (Fin 5) (V b))
  have hYX (a b : Fin 5) : (Y a * X b).IsHomogeneous 1 := by
    simpa only [mul_comm] using hXY b a
  let Z := X 0 * Y 0
  let d := X 1 * Y 0 - Y 1 * X 0
  let t := X 2 * Y 0 - Y 2 * X 0
  let s := X 1 * Y 0 + Y 1 * X 0
  let k := X 3 * Y 0 + Y 3 * X 0
  have hZ : (Z).IsHomogeneous 1 := hXY 0 0
  have hd : (d).IsHomogeneous 1 := (hXY 1 0).sub (hYX 1 0)
  have ht : (t).IsHomogeneous 1 := (hXY 2 0).sub (hYX 2 0)
  have hs : (s).IsHomogeneous 1 := (hXY 1 0).add (hYX 1 0)
  have hk : (k).IsHomogeneous 1 := (hXY 3 0).add (hYX 3 0)
  have hm : ((2 * X 1 * Y 0 + Y 1 * X 0)).IsHomogeneous 1 := by
    simpa only [mul_assoc, Nat.cast_ofNat] using
      ((hXY 1 0).mulConstant 2).add (hYX 1 0)
  let n := -4 * (X 2 * Y 0) * d ^ 3 +
    4 * t * (2 * X 1 * Y 0 + Y 1 * X 0) * d ^ 2 - Z * t ^ 3
  have hn : (n).IsHomogeneous 4 := by
    have hn0 : ((-4 * (X 2 * Y 0) * d ^ 3)).IsHomogeneous 4 := by
      simpa only [neg_mul, Nat.cast_ofNat] using
        (((hXY 2 0).mulConstant 4).neg).mul (hd.pow 3)
    exact (hn0.add
      (((ht.mulConstant 4).mul hm).mul (hd.pow 2))).sub
        (hZ.mul (ht.pow 3))
  intro j
  change (extensionAdditionVector X Y j).IsHomogeneous 5
  fin_cases j
  · exact ((hZ.pow 2).mulConstant 4).mul (hd.pow 3)
  · exact (((hZ.pow 2).mul hd).mul (ht.pow 2)).sub
      (((hZ.mulConstant 4).mul hs).mul (hd.pow 3))
  · exact hZ.mul hn
  · exact (((hZ.mulConstant 4).mul hk).mul (hd.pow 3)).add
      ((((hZ.pow 2).mulConstant 2).mul (hd.pow 2)).mul ht)
  · exact (((hk.mul hn).sub
      ((((hZ.mulConstant 2).mul (hXY 2 0)).mul ht).mul (hd.pow 2))).sub
      ((((hZ.mulConstant 2).mul (hYX 1 0)).mul (ht.pow 2)).mul hd)).add
      (((hs.pow 2).mulConstant 8).mul (hd.pow 3))

private theorem extensionAffineTranslationPolynomials_eval (Y X : Fin 5 → ℂ) (j : Fin 5) :
    MvPolynomial.eval X (extensionAffineTranslationPolynomials Y j) =
      extensionAdditionVector X Y j := by
  fin_cases j <;> simp [extensionAffineTranslationPolynomials, extensionAdditionVector]

/-- Translation by an affine elliptic point with nonzero derivative is regular
at every point of the extension surface. All three coordinate charts are used. -/
theorem projective_extension_translation_atlas
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)

    (v t : ℂ) (hv : v ∉ L.lattice) (hvder : L.derivWeierstrassP v ≠ 0) :
    ∀ p : ProjectiveExtensionChartLocus L.g₂ L.g₃,
      ∃ d : ℕ, ∃ P : Fin 5 → MvPolynomial (Fin 5) ℂ,
        (∀ j, (P j).IsHomogeneous d) ∧
        (fun j => MvPolynomial.eval p.val.val.rep (P j)) ≠ 0 ∧
        ∀ r : ProjectiveExtensionChartLocus L.g₂ L.g₃,
          ∀ hn : (fun j => MvPolynomial.eval r.val.val.rep (P j)) ≠ 0,
            Projectivization.mk ℂ (fun j => MvPolynomial.eval r.val.val.rep (P j)) hn =
              (r + e ((extensionPeriodGraph L.lattice η).mkQ (v, t))).val.val := by
  let q := e ((extensionPeriodGraph L.lattice η).mkQ (v, t))
  have hσ : D.sigma v ≠ 0 := by
    intro hz
    obtain ⟨j, hj⟩ := hS_ne v
    exact hj (by simp [hS_value v hv j, hz])
  obtain ⟨hQ, hPQ⟩ := he v t
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ _ hQ
  have hq (j : Fin 5) : q.val.val.rep j = a.val *
      (D.sigma v ^ 3 * ![1, L.weierstrassP v, L.derivWeierstrassP v,
        weierstrassZeta L v + t,
        L.derivWeierstrassP v * (weierstrassZeta L v + t) + 2 * L.weierstrassP v ^ 2] j) := by
    change (e ((extensionPeriodGraph L.lattice η).mkQ (v, t))).val.val.rep j = _
    rw [hPQ, ← ha]
    change a.val * entireExtensionVector S v t j = _
    rw [entireExtensionVector_value L D S hS_value v t hv]
    rfl
  have hq0 : q.val.val.rep 0 ≠ 0 := by
    simpa only [hq, Matrix.cons_val_zero, mul_one] using
      mul_ne_zero a.ne_zero (pow_ne_zero 3 hσ)
  have hq2 : q.val.val.rep 2 = L.derivWeierstrassP v * q.val.val.rep 0 := by
    simp only [hq]
    dsimp
    ring
  obtain ⟨P0, hP0, hcorrect0, hnonzero0⟩ :=
    projective_extension_origin_translation_law L D S hS hS_value hS_ne η e he v t hv
  obtain ⟨P2, hP2, hcorrect2, hnonzero2⟩ :=
    projective_extension_tangent_translation_law L D S hS hS_value hS_ne η e he v t hv
  intro p
  by_cases hp : p.val.val.rep 0 = 0
  · exact ⟨10, P0, hP0, hnonzero0 p hp, hcorrect0⟩
  · by_cases hd : p.val.val.rep 1 * q.val.val.rep 0 ≠ q.val.val.rep 1 * p.val.val.rep 0 ∨
        p.val.val.rep 2 * q.val.val.rep 0 ≠ q.val.val.rep 2 * p.val.val.rep 0
    · let P := extensionAffineTranslationPolynomials q.val.val.rep
      have hev (r : ProjectiveExtensionChartLocus L.g₂ L.g₃) :
          (fun j => MvPolynomial.eval r.val.val.rep (P j)) =
            extensionAdditionVector r.val.val.rep q.val.val.rep := by
        ext j
        exact extensionAffineTranslationPolynomials_eval _ _ _
      refine ⟨5, P, extensionAffineTranslationPolynomials_homogeneous _, ?_, ?_⟩
      · rw [hev]
        exact extensionAdditionVector_ne_zero _ _ hp hq0 hd
      · intro r hn
        simpa only [hev] using projective_extension_addition_polynomial
          L D S hS hS_value η e he r q (by simpa only [hev] using hn)
    · have heq : p.val.val.rep 2 = L.derivWeierstrassP v * p.val.val.rep 0 := by
        have hh := not_or.mp hd |>.2
        push Not at hh
        rw [hq2] at hh
        apply mul_right_cancel₀ hq0
        linear_combination hh
      have h2 : p.val.val.rep 2 + L.derivWeierstrassP v * p.val.val.rep 0 ≠ 0 := by
        rw [heq, ← two_mul]
        exact mul_ne_zero (by norm_num) (mul_ne_zero hvder hp)
      exact ⟨8, P2, hP2, hnonzero2 p hp h2, hcorrect2⟩

/-- Fixed translations by affine points with nonzero elliptic derivative are
regular on the entire projective extension. -/
theorem projective_extension_translation_regular
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)

    (v t : ℂ) (hv : v ∉ L.lattice) (hvder : L.derivWeierstrassP v ≠ 0) :
    MultiProjectiveSpace.IsRegularAlong (projectiveSpace ℂ 4) (projectiveSpace ℂ 4)
      (fun p : ProjectiveExtensionChartLocus L.g₂ L.g₃ => fun _ => p.val.val)
      (fun p => fun _ => (p + e ((extensionPeriodGraph L.lattice η).mkQ (v, t))).val.val) := by
  exact projective_regular_of_local_homogeneous _ _
    (projective_extension_translation_atlas L D S hS hS_value hS_ne η e he v t hv hvder)

end WeierstrassEllipticZeta



noncomputable section

open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

/-- The derivative of ℘ has isolated zeros on the complement of the lattice.
Its triple pole at zero rules out the identically zero alternative. -/
lemma derivWeierstrassP_eventually_ne_zero (L : PeriodPair) (v : ℂ)
    (hv : v ∉ L.lattice) :
    ∀ᶠ w in 𝓝[≠] v, L.derivWeierstrassP w ≠ 0 := by
  by_contra h
  have hf : ∃ᶠ w in 𝓝[≠] v, L.derivWeierstrassP w = 0 := by simpa using h
  have hconnected : IsPreconnected (L.lattice : Set ℂ)ᶜ :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
  have heq : Set.EqOn L.derivWeierstrassP (fun _ ↦ 0) L.latticeᶜ :=
    L.analyticOnNhd_derivWeierstrassP.eqOn_of_preconnected_of_frequently_eq
      (fun _ _ ↦ analyticAt_const) hconnected hv hf
  have hregular : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∉ L.lattice := by
    have hnhds : ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ ((L.lattice : Set ℂ) \ {0})ᶜ :=
      L.compl_lattice_sdiff_singleton_mem_nhds 0
    filter_upwards [hnhds.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hw hw0
    intro hwL
    exact hw ⟨hwL, hw0⟩
  have hnear : L.derivWeierstrassP =ᶠ[𝓝[≠] (0 : ℂ)] (fun _ ↦ 0) :=
    hregular.mono fun w hw ↦ heq hw
  have ho := meromorphicOrderAt_congr hnear
  have hpole : meromorphicOrderAt L.derivWeierstrassP 0 = ((-3 : ℤ) : WithTop ℤ) := by
    rw [← L.deriv_weierstrassP]
    exact meromorphicOrderAt_deriv (n := -3) (by norm_num)
      (by simpa using L.order_weierstrassP 0 L.lattice.zero_mem)
  rw [hpole, meromorphicOrderAt_const] at ho
  norm_num at ho

private lemma second_derivative_of_ne_zero (L : PeriodPair) (v : ℂ)
    (hv : v ∉ L.lattice) (hne : L.derivWeierstrassP v ≠ 0) :
    deriv L.derivWeierstrassP v = 6 * L.weierstrassP v ^ 2 - L.g₂ / 2 := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hP : HasDerivAt L.weierstrassP (L.derivWeierstrassP v) v := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (hopen.mem_nhds hv)).hasDerivAt
  have hD := (L.differentiableOn_derivWeierstrassP.differentiableAt
    (hopen.mem_nhds hv)).hasDerivAt
  have hnear : ∀ᶠ w in 𝓝 v, w ∉ L.lattice := hopen.mem_nhds hv
  have heq : (fun w ↦ L.derivWeierstrassP w ^ 2) =ᶠ[𝓝 v]
      (fun w ↦ 4 * L.weierstrassP w ^ 3 - L.g₂ * L.weierstrassP w - L.g₃) :=
    hnear.mono fun w hw ↦ L.derivWeierstrassP_sq w hw
  have hh := ((hD.pow 2).congr_of_eventuallyEq heq.symm).unique
    ((((hP.pow 3).const_mul 4).sub (hP.const_mul L.g₂)).sub_const L.g₃)
  have hprod : L.derivWeierstrassP v *
      (deriv L.derivWeierstrassP v - (6 * L.weierstrassP v ^ 2 - L.g₂ / 2)) = 0 := by
    linear_combination hh / 2
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hne)

/-- The second-order differential equation holds at every regular point,
including zeros of ℘′. -/
theorem hasDerivAt_derivWeierstrassP (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    HasDerivAt L.derivWeierstrassP (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) z := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hD := L.differentiableOn_derivWeierstrassP.differentiableAt (hopen.mem_nhds hz)
  have hleft : ContinuousAt (deriv L.derivWeierstrassP) z :=
    (L.analyticOnNhd_derivWeierstrassP z hz).deriv.continuousAt
  have hright : ContinuousAt (fun w ↦ 6 * L.weierstrassP w ^ 2 - L.g₂ / 2) z :=
    ((L.analyticOnNhd_weierstrassP z hz).continuousAt.pow 2 |>.const_mul 6).sub
      continuousAt_const
  have hnear : ∀ᶠ w in 𝓝 z, w ∉ L.lattice := hopen.mem_nhds hz
  have heq : deriv L.derivWeierstrassP =ᶠ[𝓝[≠] z]
      (fun w ↦ 6 * L.weierstrassP w ^ 2 - L.g₂ / 2) := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
      derivWeierstrassP_eventually_ne_zero L z hz] with w hw hne
    exact second_derivative_of_ne_zero L w hw hne
  have hvalue := tendsto_nhds_unique (hleft.tendsto.mono_left nhdsWithin_le_nhds)
    ((hright.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)
  exact hD.hasDerivAt.congr_deriv hvalue

end WeierstrassEllipticZeta


set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
open scoped Topology
namespace WeierstrassEllipticZeta

private theorem shifted_eventually_regular (L : PeriodPair) (a z : ℂ) :
    ∀ᶠ r in 𝓝[≠] a, z + r ∉ L.lattice := by
  have hn : ∀ᶠ w in 𝓝 (z + a), w ∈ ((L.lattice : Set ℂ) \ {z + a})ᶜ :=
    L.compl_lattice_sdiff_singleton_mem_nhds (z + a)
  have ht := (continuousAt_const.add continuousAt_id).eventually hn
  filter_upwards [ht.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr hra
  intro hL
  exact hr ⟨hL, fun h => hra (add_left_cancel h)⟩

/-- Opposite translations can put any two elliptic parameters in the affine
addition chart, while both translating parameters have nonzero derivative. -/
theorem exists_regular_addition_shift (L : PeriodPair) (z v : ℂ) :
    ∃ r : ℂ, r ∉ L.lattice ∧ L.derivWeierstrassP r ≠ 0 ∧
      z + r ∉ L.lattice ∧ v - r ∉ L.lattice ∧
      (L.weierstrassP (z + r) ≠ L.weierstrassP (v - r) ∨
       L.derivWeierstrassP (z + r) ≠ L.derivWeierstrassP (v - r)) := by
  let a := L.ω₁ / 2
  have ha : a ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have h0 : ∀ᶠ r in 𝓝[≠] a, r ∉ L.lattice := by
    have hh : ∀ᶠ r in 𝓝 a, r ∉ L.lattice := L.isClosed_lattice.isOpen_compl.mem_nhds ha
    exact hh.filter_mono nhdsWithin_le_nhds
  have h1 := derivWeierstrassP_eventually_ne_zero L a ha
  have h2 := shifted_eventually_regular L a z
  have h3 : ∀ᶠ r in 𝓝[≠] a, v - r ∉ L.lattice := by
    have hn : ∀ᶠ w in 𝓝 (v - a), w ∈ ((L.lattice : Set ℂ) \ {v - a})ᶜ :=
      L.compl_lattice_sdiff_singleton_mem_nhds (v - a)
    have ht := (continuousAt_const.sub continuousAt_id).eventually hn
    filter_upwards [ht.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr hra
    intro hL
    exact hr ⟨hL, fun h => hra (sub_right_injective h)⟩
  obtain ⟨a, ha, ha', hza, hva⟩ := (h0.and (h1.and (h2.and h3))).exists
  have hza' : ∀ᶠ r in 𝓝[≠] a, L.derivWeierstrassP (z + r) ≠ 0 :=
    ((hasDerivAt_id a).const_add z).tendsto_nhdsNE (by norm_num) |>.eventually
      (derivWeierstrassP_eventually_ne_zero L (z + a) hza)
  have hgood : ∀ᶠ r in 𝓝 a,
      r ∉ L.lattice ∧ L.derivWeierstrassP r ≠ 0 ∧
        z + r ∉ L.lattice ∧ v - r ∉ L.lattice := by
    have hreg := L.isClosed_lattice.isOpen_compl
    filter_upwards [hreg.mem_nhds ha,
      (L.analyticOnNhd_derivWeierstrassP a ha).continuousAt.eventually_ne ha',
      (continuousAt_const.add continuousAt_id).eventually (hreg.mem_nhds hza),
      (continuousAt_const.sub continuousAt_id).eventually (hreg.mem_nhds hva)]
      with r hr hr' hzr hvr
    exact ⟨hr, hr', hzr, hvr⟩
  obtain ⟨a, ⟨ha, ha', hza, hva⟩, hza'⟩ :=
    ((hgood.filter_mono nhdsWithin_le_nhds).and hza').exists
  by_cases hp : L.weierstrassP (z + a) ≠ L.weierstrassP (v - a)
  · exact ⟨a, ha, ha', hza, hva, Or.inl hp⟩
  by_cases hd : L.derivWeierstrassP (z + a) ≠ L.derivWeierstrassP (v - a)
  · exact ⟨a, ha, ha', hza, hva, Or.inr hd⟩
  have hdp : HasDerivAt (fun r : ℂ => L.weierstrassP (z + r))
      (L.derivWeierstrassP (z + a)) a := by
    have h : HasDerivAt L.weierstrassP (L.derivWeierstrassP (z + a)) (z + a) := by
      simpa using (L.analyticOnNhd_weierstrassP (z + a) hza).differentiableAt.hasDerivAt
    simpa [Function.comp_def] using! h.comp a ((hasDerivAt_id a).const_add z)
  have hdm : HasDerivAt (fun r : ℂ => L.weierstrassP (v - r))
      (-L.derivWeierstrassP (v - a)) a := by
    have h : HasDerivAt L.weierstrassP (L.derivWeierstrassP (v - a)) (v - a) := by
      simpa using (L.analyticOnNhd_weierstrassP (v - a) hva).differentiableAt.hasDerivAt
    simpa [Function.comp_def] using! h.comp a ((hasDerivAt_id a).const_sub v)
  have hder : L.derivWeierstrassP (z + a) - -L.derivWeierstrassP (v - a) ≠ 0 := by
    rw [not_not.mp hd, sub_neg_eq_add, ← two_mul]
    exact mul_ne_zero (by norm_num) (by simpa only [not_not.mp hd] using hza')
  have hsep := (hdp.sub hdm).eventually_ne (c := 0) hder
  have hreg := L.isClosed_lattice.isOpen_compl
  have hgood : ∀ᶠ r in 𝓝 a,
      r ∉ L.lattice ∧ L.derivWeierstrassP r ≠ 0 ∧
        z + r ∉ L.lattice ∧ v - r ∉ L.lattice := by
    filter_upwards [hreg.mem_nhds ha,
      (L.analyticOnNhd_derivWeierstrassP a ha).continuousAt.eventually_ne ha',
      (continuousAt_const.add continuousAt_id).eventually (hreg.mem_nhds hza),
      (continuousAt_const.sub continuousAt_id).eventually (hreg.mem_nhds hva)]
      with r hr hr' hzr hvr
    exact ⟨hr, hr', hzr, hvr⟩
  obtain ⟨r, ⟨hr, hr', hzr, hvr⟩, hsep⟩ :=
    ((hgood.filter_mono nhdsWithin_le_nhds).and hsep).exists
  exact ⟨r, hr, hr', hzr, hvr, Or.inl (sub_ne_zero.mp hsep)⟩

end WeierstrassEllipticZeta


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem IsHomogeneous.mul_weighted {P Q : M.CoordinateRing}
    {D : M.FactorIndex → ℕ} {a b : ℕ}
    (hP : M.IsHomogeneous P (fun i => a * D i))
    (hQ : M.IsHomogeneous Q (fun i => b * D i)) :
    M.IsHomogeneous (P * Q) (fun i => (a + b) * D i) := by
  simpa only [Pi.add_def, Nat.add_mul] using hP.mul M hQ

theorem IsHomogeneous.pow_weighted {P : M.CoordinateRing}
    {D : M.FactorIndex → ℕ} {a : ℕ}
    (hP : M.IsHomogeneous P (fun i => a * D i)) (n : ℕ) :
    M.IsHomogeneous (P ^ n) (fun i => (n * a) * D i) := by
  simpa only [Nat.mul_assoc] using hP.pow M n

end PhilipponMultiplicity.MultiProjectiveSpace
namespace WeierstrassEllipticZeta
open PhilipponMultiplicity

/-- Substituting homogeneous coordinate tuples preserves the common
multidegree of the addition law. -/
theorem extensionAdditionVector_homogeneous (M : MultiProjectiveSpace ℂ)
    (X Y : Fin 5 → M.CoordinateRing) (D : M.FactorIndex → ℕ)
    (hXY : ∀ a b, M.IsHomogeneous (X a * Y b) (fun i => 1 * D i)) :
    ∀ j, M.IsHomogeneous (extensionAdditionVector X Y j) (fun i => 5 * D i) := by
  have hYX (a b : Fin 5) : M.IsHomogeneous (Y a * X b) (fun i => 1 * D i) := by
    simpa only [mul_comm] using hXY b a
  let Z := X 0 * Y 0
  let d := X 1 * Y 0 - Y 1 * X 0
  let t := X 2 * Y 0 - Y 2 * X 0
  let s := X 1 * Y 0 + Y 1 * X 0
  let k := X 3 * Y 0 + Y 3 * X 0
  have hZ : M.IsHomogeneous Z (fun i => 1 * D i) := hXY 0 0
  have hd : M.IsHomogeneous d (fun i => 1 * D i) := (hXY 1 0).sub M (hYX 1 0)
  have ht : M.IsHomogeneous t (fun i => 1 * D i) := (hXY 2 0).sub M (hYX 2 0)
  have hs : M.IsHomogeneous s (fun i => 1 * D i) := (hXY 1 0).add M (hYX 1 0)
  have hk : M.IsHomogeneous k (fun i => 1 * D i) := (hXY 3 0).add M (hYX 3 0)
  have hm : M.IsHomogeneous (2 * X 1 * Y 0 + Y 1 * X 0) (fun i => 1 * D i) := by
    simpa only [mul_assoc, Nat.cast_ofNat] using
      ((hXY 1 0).nat_mul M 2).add M (hYX 1 0)
  let n := -4 * (X 2 * Y 0) * d ^ 3 +
    4 * t * (2 * X 1 * Y 0 + Y 1 * X 0) * d ^ 2 - Z * t ^ 3
  have hn : M.IsHomogeneous n (fun i => 4 * D i) := by
    have hn0 : M.IsHomogeneous (-4 * (X 2 * Y 0) * d ^ 3) (fun i => 4 * D i) := by
      simpa only [neg_mul, Nat.cast_ofNat, Pi.add_def, Nat.mul_one] using
        (((hXY 2 0).nat_mul M 4).neg M).mul_weighted M (hd.pow_weighted M 3)
    exact (hn0.add M
      (((ht.nat_mul M 4).mul_weighted M hm).mul_weighted M (hd.pow_weighted M 2))).sub M
        (hZ.mul_weighted M (ht.pow_weighted M 3))
  intro j
  change M.IsHomogeneous (extensionAdditionVector X Y j) (fun i => 5 * D i)
  fin_cases j
  · exact ((hZ.pow_weighted M 2).nat_mul M 4).mul_weighted M (hd.pow_weighted M 3)
  · exact (((hZ.pow_weighted M 2).mul_weighted M hd).mul_weighted M (ht.pow_weighted M 2)).sub M
      (((hZ.nat_mul M 4).mul_weighted M hs).mul_weighted M (hd.pow_weighted M 3))
  · exact hZ.mul_weighted M hn
  · exact (((hZ.nat_mul M 4).mul_weighted M hk).mul_weighted M (hd.pow_weighted M 3)).add M
      ((((hZ.pow_weighted M 2).nat_mul M 2).mul_weighted M (hd.pow_weighted M 2)).mul_weighted M ht)
  · exact (((hk.mul_weighted M hn).sub M
      ((((hZ.nat_mul M 2).mul_weighted M (hXY 2 0)).mul_weighted M ht).mul_weighted M (hd.pow_weighted M 2))).sub M
      ((((hZ.nat_mul M 2).mul_weighted M (hYX 1 0)).mul_weighted M (ht.pow_weighted M 2)).mul_weighted M hd)).add M
      (((hs.pow_weighted M 2).nat_mul M 8).mul_weighted M (hd.pow_weighted M 3))

end WeierstrassEllipticZeta


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open TranscendenceTheory PhilipponMultiplicity
namespace WeierstrassEllipticZeta


private theorem addition_vector_map {K T : Type*} [CommRing K] [CommRing T]
    (f : K →+* T) (X Y : Fin 5 → K) :
    (fun j => f (extensionAdditionVector X Y j)) =
      extensionAdditionVector (fun j => f (X j)) (fun j => f (Y j)) := by
  ext j
  fin_cases j <;> simp [extensionAdditionVector, map_ofNat]

section
variable
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)

include hS_value hS_ne he in
private theorem projective_extension_parameter_rep (z u : ℂ) (hz : z ∉ L.lattice) :
    ∃ a : ℂ, a ≠ 0 ∧
      (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val.rep =
        a • ![1, L.weierstrassP z, L.derivWeierstrassP z, weierstrassZeta L z + u,
          L.derivWeierstrassP z * (weierstrassZeta L z + u) + 2 * L.weierstrassP z ^ 2] := by
  have hσ : D.sigma z ≠ 0 := by
    intro hzero
    obtain ⟨j, hj⟩ := hS_ne z
    exact hj (by simp [hS_value z hz j, hzero])
  obtain ⟨hX, hPX⟩ := he z u
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ _ hX
  refine ⟨a.val * D.sigma z ^ 3, mul_ne_zero a.ne_zero (pow_ne_zero _ hσ), ?_⟩
  rw [hPX, ← ha]
  change a.val • entireExtensionVector S z u = _
  rw [entireExtensionVector_value L D S hS_value z u hz, smul_smul]

include hS_value hS_ne he in
private theorem exists_addition_chart_shift (p q : ProjectiveExtensionChartLocus L.g₂ L.g₃) :
    ∃ r : ℂ, r ∉ L.lattice ∧ L.derivWeierstrassP r ≠ 0 ∧
      let R := e ((extensionPeriodGraph L.lattice η).mkQ (r, 0))
      (p + R).val.val.rep 0 ≠ 0 ∧ (q - R).val.val.rep 0 ≠ 0 ∧
      ((p + R).val.val.rep 1 * (q - R).val.val.rep 0 ≠
          (q - R).val.val.rep 1 * (p + R).val.val.rep 0 ∨
       (p + R).val.val.rep 2 * (q - R).val.val.rep 0 ≠
          (q - R).val.val.rep 2 * (p + R).val.val.rep 0) := by
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  obtain ⟨⟨z, u⟩, rfl⟩ := (extensionPeriodGraph L.lattice η).mkQ_surjective p
  obtain ⟨⟨v, t⟩, rfl⟩ := (extensionPeriodGraph L.lattice η).mkQ_surjective q
  obtain ⟨r, hr, hr', hzr, hvr, hsep⟩ := exists_regular_addition_shift L z v
  refine ⟨r, hr, hr', ?_⟩
  dsimp only
  have hp : e ((extensionPeriodGraph L.lattice η).mkQ (z, u)) +
      e ((extensionPeriodGraph L.lattice η).mkQ (r, 0)) =
      e ((extensionPeriodGraph L.lattice η).mkQ (z + r, u)) := by
    rw [← map_add, ← map_add]
    simp
  have hq : e ((extensionPeriodGraph L.lattice η).mkQ (v, t)) -
      e ((extensionPeriodGraph L.lattice η).mkQ (r, 0)) =
      e ((extensionPeriodGraph L.lattice η).mkQ (v - r, t)) := by
    rw [← map_sub, ← map_sub]
    simp
  rw [hp, hq]
  obtain ⟨a, ha, hpa⟩ := projective_extension_parameter_rep L D S hS_value hS_ne η e he
    (z + r) u hzr
  obtain ⟨b, hb, hqb⟩ := projective_extension_parameter_rep L D S hS_value hS_ne η e he
    (v - r) t hvr
  rw [hpa, hqb]
  simp only [Pi.smul_apply, smul_eq_mul]
  dsimp
  simp only [mul_one]
  refine ⟨ha, hb, ?_⟩
  rcases hsep with hsep | hsep
  · left
    intro hh
    apply hsep
    apply mul_left_cancel₀ (mul_ne_zero ha hb)
    linear_combination hh
  · right
    intro hh
    apply hsep
    apply mul_left_cancel₀ (mul_ne_zero ha hb)
    linear_combination hh

include hS hS_value he in
private theorem addition_vector_represents_sum
    (p q : ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (X Y : Fin 5 → ℂ) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hp : Projectivization.mk ℂ X hX = p.val.val)
    (hq : Projectivization.mk ℂ Y hY = q.val.val)
    (hn : extensionAdditionVector X Y ≠ 0) :
    Projectivization.mk ℂ (extensionAdditionVector X Y) hn = (p + q).val.val := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ X hX
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ Y hY
  have heq : extensionAdditionVector p.val.val.rep q.val.val.rep =
      (a.val ^ 5 * b.val ^ 5) • extensionAdditionVector X Y := by
    rw [← hp, ← hq, ← ha, ← hb]
    exact extensionAdditionVector_smul X Y a.val b.val
  have hc : a.val ^ 5 * b.val ^ 5 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ a.ne_zero) (pow_ne_zero _ b.ne_zero)
  have hne : extensionAdditionVector p.val.val.rep q.val.val.rep ≠ 0 := by
    rw [heq]
    exact smul_ne_zero hc hn
  rw [← projective_extension_addition_polynomial L D S hS hS_value η e he p q hne]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(a.val ^ 5 * b.val ^ 5)⁻¹, ?_⟩
  rw [heq, smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem addition_vector_ne_zero_of_representatives
    (p q : Projectivization ℂ (Fin 5 → ℂ))
    (X Y : Fin 5 → ℂ) (hX : X ≠ 0) (hY : Y ≠ 0)
    (hp : Projectivization.mk ℂ X hX = p)
    (hq : Projectivization.mk ℂ Y hY = q)
    (hp0 : p.rep 0 ≠ 0) (hq0 : q.rep 0 ≠ 0)
    (hsep : p.rep 1 * q.rep 0 ≠ q.rep 1 * p.rep 0 ∨
      p.rep 2 * q.rep 0 ≠ q.rep 2 * p.rep 0) :
    extensionAdditionVector X Y ≠ 0 := by
  intro hz
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ X hX
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ Y hY
  apply extensionAdditionVector_ne_zero p.rep q.rep hp0 hq0 hsep
  rw [← hp, ← hq, ← ha, ← hb]
  change extensionAdditionVector (a.val • X) (b.val • Y) = 0
  rw [extensionAdditionVector_smul, hz, smul_zero]

end

/-- The projective extension has a regular two-variable addition operation.
This proves the complete addition field of the embedded-group model. -/
theorem projective_extension_addition_regular_implementation
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)

 :
    MultiProjectiveSpace.IsRegularAlong (projectiveSquare ℂ 4) (projectiveSpace ℂ 4)
      (fun pq : ProjectiveExtensionChartLocus L.g₂ L.g₃ ×
          ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
        fun i => if i.val = 0 then pq.1.val.val else pq.2.val.val)
      (fun pq => fun _ => (pq.1 + pq.2).val.val) := by
  let M := projectiveSquare ℂ 4
  apply multiprojective_regular_of_local_homogeneous M
  rintro ⟨p, q⟩
  obtain ⟨r, hr, hr', hp0, hq0, hsep⟩ :=
    exists_addition_chart_shift L D S hS_value hS_ne η e he p q
  let R := e ((extensionPeriodGraph L.lattice η).mkQ (r, 0))
  have hminus : e ((extensionPeriodGraph L.lattice η).mkQ (-r, 0)) = -R := by
    change e ((extensionPeriodGraph L.lattice η).mkQ (-r, 0)) =
      -e ((extensionPeriodGraph L.lattice η).mkQ (r, 0))
    rw [← map_neg, ← map_neg]
    simp
  have hrneg : -r ∉ L.lattice := by simpa using hr
  have hrneg' : L.derivWeierstrassP (-r) ≠ 0 := by simpa using hr'
  obtain ⟨d, P, hP, hnP, hcP⟩ :=
    projective_extension_translation_atlas L D S hS hS_value hS_ne η e he r 0 hr hr' p
  obtain ⟨f, Q, hQ, hnQ, hcQ⟩ :=
    projective_extension_translation_atlas L D S hS hS_value hS_ne η e he (-r) 0 hrneg hrneg' q
  let P' : Fin 5 → M.CoordinateRing :=
    fun j => MvPolynomial.rename (fun k => ⟨(0 : Fin 2), k⟩) (P j)
  let Q' : Fin 5 → M.CoordinateRing :=
    fun j => MvPolynomial.rename (fun k => ⟨(1 : Fin 2), k⟩) (Q j)
  let A := extensionAdditionVector P' Q'
  let degrees : M.FactorIndex → ℕ := fun i =>
    (if i = (0 : Fin 2) then d else 0) + (if i = (1 : Fin 2) then f else 0)
  have hA : ∀ j, M.IsHomogeneous (A j) (fun i => 5 * degrees i) := by
    apply extensionAdditionVector_homogeneous
    intro i j
    simp only [Nat.one_mul]
    exact (block_isHomogeneous M (0 : Fin 2) (hP i)).mul M
      (block_isHomogeneous M (1 : Fin 2) (hQ j))
  have hev (p q : ProjectiveExtensionChartLocus L.g₂ L.g₃) :
      (fun j => M.eval (A j) (fun i => if i.val = 0 then p.val.val else q.val.val)) =
        extensionAdditionVector (fun j => MvPolynomial.eval p.val.val.rep (P j))
          (fun j => MvPolynomial.eval q.val.val.rep (Q j)) := by
    have hp (j : Fin 5) :
        M.eval (P' j) (fun i => if i.val = 0 then p.val.val else q.val.val) =
          MvPolynomial.eval p.val.val.rep (P j) := by
      change MvPolynomial.eval _ (MvPolynomial.rename _ (P j)) = _
      rw [MvPolynomial.eval_rename]
      rfl
    have hq (j : Fin 5) :
        M.eval (Q' j) (fun i => if i.val = 0 then p.val.val else q.val.val) =
          MvPolynomial.eval q.val.val.rep (Q j) := by
      change MvPolynomial.eval _ (MvPolynomial.rename _ (Q j)) = _
      rw [MvPolynomial.eval_rename]
      rfl
    change (fun j => (MvPolynomial.eval (M.coordinate
      (fun i => if i.val = 0 then p.val.val else q.val.val)))
        (extensionAdditionVector P' Q' j)) = _
    rw [addition_vector_map]
    congr 1 <;> funext j
    · exact hp j
    · exact hq j
  refine ⟨fun i => 5 * degrees i, A, hA, ?_, ?_⟩
  · rw [hev]
    have hPQ := hcQ q hnQ
    rw [hminus, ← sub_eq_add_neg] at hPQ
    exact addition_vector_ne_zero_of_representatives _ _ _ _ hnP hnQ
      (hcP p hnP) hPQ hp0 hq0 hsep
  · rintro ⟨p, q⟩ hn
    change (fun j : Fin 5 => M.eval (A j)
      (fun i : Fin 2 => if i.val = 0 then p.val.val else q.val.val)) ≠ 0 at hn
    change Projectivization.mk ℂ (fun j : Fin 5 => M.eval (A j)
      (fun i : Fin 2 => if i.val = 0 then p.val.val else q.val.val)) hn = (p + q).val.val
    have hn' : extensionAdditionVector (fun j => MvPolynomial.eval p.val.val.rep (P j))
        (fun j => MvPolynomial.eval q.val.val.rep (Q j)) ≠ 0 := by
      intro hz
      exact hn ((hev p q).trans hz)
    have hnp : (fun j => MvPolynomial.eval p.val.val.rep (P j)) ≠ 0 := by
      intro hz
      apply hn'
      rw [hz]
      ext j
      fin_cases j <;> simp [extensionAdditionVector]
    have hnq : (fun j => MvPolynomial.eval q.val.val.rep (Q j)) ≠ 0 := by
      intro hz
      apply hn'
      rw [hz]
      ext j
      fin_cases j <;> simp [extensionAdditionVector]
    have hPQ := hcQ q hnq
    rw [hminus, ← sub_eq_add_neg] at hPQ
    have hh := addition_vector_represents_sum L D S hS hS_value η e he
      (p + R) (q - R) _ _ hnp hnq (hcP p hnp) hPQ hn'
    have hcancel : p + R + (q - R) = p + q := by abel
    rw [hcancel] at hh
    refine Eq.trans ?_ hh
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨1, ?_⟩
    rw [one_smul]
    exact (hev p q).symm


end WeierstrassEllipticZeta
open WeierstrassEllipticZeta TranscendenceTheory PhilipponMultiplicity
theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    [AddCommGroup (ProjectiveExtensionChartLocus L.g₂ L.g₃)]
    (e : GraphQuotientExtension L.lattice η ≃+ ProjectiveExtensionChartLocus L.g₂ L.g₃)
    (he : ∀ z u : ℂ, ∃ hv :
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] ≠ 0,
        (e ((extensionPeriodGraph L.lattice η).mkQ (z, u))).val.val = Projectivization.mk ℂ
          ![S 0 z, S 1 z, S 2 z, S 3 z + u * S 0 z, S 4 z + u * S 2 z] hv)

 :
    MultiProjectiveSpace.IsRegularAlong (projectiveSquare ℂ 4) (projectiveSpace ℂ 4)
      (fun pq : ProjectiveExtensionChartLocus L.g₂ L.g₃ ×
          ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
        fun i => if i.val = 0 then pq.1.val.val else pq.2.val.val)
      (fun pq => fun _ => (pq.1 + pq.2).val.val) := by
  exact WeierstrassEllipticZeta.projective_extension_addition_regular_implementation L D S hS hS_value hS_ne η e he
