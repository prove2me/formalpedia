-- Prove2me | solution 1 for WheelerDeWittSuperspace.kinetic_volume_sector
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-09T21:57:42.977142+00:00
-- url     : https://prove2.me/submissions/5dacb809-ce5d-48fe-af65-0867c31d370f

import Definitions.Def_WheelerDeWittSuperspace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Adjugate

set_option autoImplicit false

open Matrix

namespace WheelerDeWittSuperspace

noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X]


def Cf (m : Matrix (Fin 3) (Fin 3) ℝ) (a b c d : Fin 3) : ℝ :=
  if a = c then 0 else adjugate (m.updateRow c (Pi.single d 1)) b a

theorem sym_eq (m : Matrix (Fin 3) (Fin 3) ℝ) (hs : ∀ i j, m i j = m j i) :
    m = !![m 0 0, m 0 1, m 0 2; m 0 1, m 1 1, m 1 2; m 0 2, m 1 2, m 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> first | rfl | exact hs _ _

theorem P1 (m : Matrix (Fin 3) (Fin 3) ℝ) (hs : ∀ i j, m i j = m j i) :
    ∑ a, ∑ b, ∑ c, ∑ d, (m a c * m b d + m a d * m b c - m a b * m c d) *
      adjugate m b a * adjugate m d c = -3 * m.det ^ 2 := by
  rw [sym_eq m hs]
  simp [Fin.sum_univ_three, adjugate_fin_three, det_fin_three]
  ring

theorem P2 (m : Matrix (Fin 3) (Fin 3) ℝ) (hs : ∀ i j, m i j = m j i) :
    ∑ a, ∑ b, ∑ c, ∑ d, (m a c * m b d + m a d * m b c - m a b * m c d) *
      Cf m a b c d = -12 * m.det := by
  rw [sym_eq m hs]
  simp [Cf, Fin.sum_univ_three, adjugate_fin_three, det_fin_three, updateRow_apply,
    Pi.single_apply]
  ring


theorem cd_det (z : X) : ContDiff ℝ ⊤ (fun h : Config X => (metricAt h z).det) := by
  simp only [metricAt, Matrix.det_fin_three, Matrix.of_apply]
  fun_prop

theorem diff_adj (z : X) (c d : Fin 3) :
    Differentiable ℝ (fun h : Config X => adjugate (metricAt h z) d c) := by
  fin_cases c <;> fin_cases d <;>
    simp [adjugate_fin_three, metricAt] <;> fun_prop

theorem fderiv_eq_deriv_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Config X → F} {w : Config X} (hG : DifferentiableAt ℝ G w) (v : Config X) :
    fderiv ℝ G w v = deriv (fun t : ℝ => G (w + t • v)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
  have hd' : HasFDerivAt G (fderiv ℝ G w) (w + (0 : ℝ) • v) := by simpa using hG.hasFDerivAt
  exact ((hd'.comp_hasDerivAt (0 : ℝ) hl).deriv).symm

theorem metricAt_line (h : Config X) (x : X) (t : ℝ) (c d : Fin 3) :
    metricAt (h + t • coordDir x c d) x =
      (metricAt h x).updateRow c (metricAt h x c + t • Pi.single d 1) := by
  ext i j
  by_cases hi : i = c
  · subst hi
    by_cases hj : j = d
    · subst hj; simp [metricAt, coordDir, updateRow_apply]
    · simp [metricAt, coordDir, updateRow_apply, hj, Pi.single_apply]
  · simp [metricAt, coordDir, updateRow_apply, hi]

theorem det_line (h : Config X) (x : X) (t : ℝ) (c d : Fin 3) :
    (metricAt (h + t • coordDir x c d) x).det =
      (metricAt h x).det + t * adjugate (metricAt h x) d c := by
  rw [metricAt_line, det_updateRow_add, det_updateRow_smul, updateRow_eq_self, adjugate_apply]

theorem adj_line (h : Config X) (x : X) (t : ℝ) (a b c d : Fin 3) :
    adjugate (metricAt (h + t • coordDir x a b) x) d c =
      adjugate (metricAt h x) d c + t * Cf (metricAt h x) a b c d := by
  rw [metricAt_line, adjugate_apply, adjugate_apply, Cf]
  generalize metricAt h x = m
  split_ifs with hac
  · subst hac; rw [updateRow_idem]; ring
  · rw [updateRow_comm _ hac, ← updateRow_ne (M := m) (b := Pi.single d 1) hac,
      det_updateRow_add, det_updateRow_smul, updateRow_eq_self, adjugate_apply]


def Fcd (f : ℝ → ℂ) (x : X) (c d : Fin 3) (h : Config X) : ℂ :=
  deriv f (volume (metricAt h x)) *
    ((adjugate (metricAt h x) d c / (2 * volume (metricAt h x)) : ℝ) : ℂ)

theorem hasDerivAt_sqrt_line (D A : ℝ) (hD : 0 < D) :
    HasDerivAt (fun t : ℝ => Real.sqrt (D + t * A)) (A / (2 * Real.sqrt D)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => D + t * A) A 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const A).const_add D
  simpa using h1.sqrt (by simpa using hD.ne')

theorem pD_vol (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (x : X) (c d : Fin 3) {h : Config X}
    (hd : 0 < (metricAt h x).det) :
    partialD (fun h' => f (volume (metricAt h' x))) x c d h = Fcd f x c d h := by
  have hdiff : DifferentiableAt ℝ (fun h' => f (volume (metricAt h' x))) h :=
    ((hf.differentiable (by simp)) _).comp h
      (((cd_det x).differentiable (by simp) h).sqrt hd.ne')
  unfold partialD
  rw [fderiv_eq_deriv_line hdiff]
  simp only [volume, det_line]
  have h3 := HasDerivAt.scomp (x := (0 : ℝ))
    ((hf.differentiable (by simp)) (Real.sqrt ((metricAt h x).det + 0 *
      adjugate (metricAt h x) d c))).hasDerivAt
    (hasDerivAt_sqrt_line _ (adjugate (metricAt h x) d c) hd)
  rw [show (fun t : ℝ => f (Real.sqrt ((metricAt h x).det + t * adjugate (metricAt h x) d c)))
    = f ∘ (fun t : ℝ => Real.sqrt ((metricAt h x).det + t * adjugate (metricAt h x) d c))
    from rfl, h3.deriv]
  simp [Fcd, volume, Complex.real_smul]
  ring

theorem diff_Fcd (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (x : X) (c d : Fin 3) {h : Config X}
    (hd : 0 < (metricAt h x).det) : DifferentiableAt ℝ (Fcd f x c d) h := by
  have hdf : Differentiable ℝ (deriv f) :=
    ((contDiff_succ_iff_deriv (n := 1)).mp (by simpa [one_add_one_eq_two] using hf)).2.2.differentiable
      (by simp)
  have hdv : DifferentiableAt ℝ (fun h' : Config X => volume (metricAt h' x)) h :=
    ((cd_det x).differentiable (by simp) h).sqrt hd.ne'
  have hv : 0 < volume (metricAt h x) := Real.sqrt_pos.2 hd
  have hr : DifferentiableAt ℝ (fun h' : Config X =>
      adjugate (metricAt h' x) d c / (2 * volume (metricAt h' x))) h := by
    have ha : DifferentiableAt ℝ (fun h' : Config X => adjugate (metricAt h' x) d c) h :=
      diff_adj x c d h
    fun_prop (disch := simp [hv.ne'])
  exact ((hdf _).comp h hdv).mul
    ((Complex.ofRealCLM.hasFDerivAt (x := _)).comp h hr.hasFDerivAt).differentiableAt

theorem step2 (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (x : X) (a b c d : Fin 3) (h : Config X)
    (hd : 0 < (metricAt h x).det) :
    partialD (partialD (fun h' => f (volume (metricAt h' x))) x c d) x a b h =
      iteratedDeriv 2 f (volume (metricAt h x)) *
        ((adjugate (metricAt h x) b a / (2 * volume (metricAt h x)) *
          (adjugate (metricAt h x) d c / (2 * volume (metricAt h x))) : ℝ) : ℂ) +
      deriv f (volume (metricAt h x)) *
        (((Cf (metricAt h x) a b c d * (2 * volume (metricAt h x)) -
          adjugate (metricAt h x) d c * (2 * (adjugate (metricAt h x) b a /
            (2 * volume (metricAt h x))))) / (2 * volume (metricAt h x)) ^ 2 : ℝ) : ℂ) := by
  have hev : partialD (fun h' => f (volume (metricAt h' x))) x c d =ᶠ[nhds h] Fcd f x c d := by
    have ho : IsOpen {h' : Config X | 0 < (metricAt h' x).det} :=
      isOpen_lt continuous_const (cd_det x).continuous
    filter_upwards [ho.mem_nhds hd] with h' hh' using pD_vol f hf x c d hh'
  have hdf : Differentiable ℝ (deriv f) :=
    ((contDiff_succ_iff_deriv (n := 1)).mp (by simpa [one_add_one_eq_two] using hf)).2.2.differentiable
      (by simp)
  show fderiv ℝ (partialD (fun h' => f (volume (metricAt h' x))) x c d) h (coordDir x a b) = _
  rw [hev.fderiv_eq, fderiv_eq_deriv_line (diff_Fcd f hf x c d hd)]
  simp only [Fcd, volume, det_line, adj_line]
  set D := (metricAt h x).det with hD
  set A := adjugate (metricAt h x) b a
  set B := adjugate (metricAt h x) d c
  set C := Cf (metricAt h x) a b c d
  have hg := hasDerivAt_sqrt_line D A hd
  have hv : 0 < Real.sqrt D := Real.sqrt_pos.2 hd
  have hp := HasDerivAt.scomp (x := (0 : ℝ)) (hdf (Real.sqrt (D + 0 * A))).hasDerivAt hg
  have hnum : HasDerivAt (fun t : ℝ => B + t * C) C 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const C).const_add B
  have hq := hnum.div (hg.const_mul 2) (by simp; positivity)
  have hm := hp.mul hq.ofReal_comp
  have hm' : HasDerivAt (fun t : ℝ => deriv f (Real.sqrt (D + t * A)) *
      (((B + t * C) / (2 * Real.sqrt (D + t * A)) : ℝ) : ℂ)) _ 0 := hm
  rw [hm'.deriv]
  simp [iteratedDeriv_succ, Complex.real_smul]
  ring


theorem sum_split (G r1 r2 : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (α β : ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, (G a b c d : ℂ) * (α * (r1 a b c d : ℂ) + β * (r2 a b c d : ℂ)) =
      α * ((∑ a, ∑ b, ∑ c, ∑ d, G a b c d * r1 a b c d : ℝ) : ℂ) +
        β * ((∑ a, ∑ b, ∑ c, ∑ d, G a b c d * r2 a b c d : ℝ) : ℂ) := by
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

theorem S1 (m : Matrix (Fin 3) (Fin 3) ℝ) (hs : ∀ i j, m i j = m j i) (hd : 0 < m.det) :
    ∑ a, ∑ b, ∑ c, ∑ d, deWitt m a b c d *
      (adjugate m b a / (2 * volume m) * (adjugate m d c / (2 * volume m))) =
        -3 * volume m / 8 := by
  have hv : 0 < volume m := Real.sqrt_pos.2 hd
  have hv2 : volume m ^ 2 = m.det := Real.sq_sqrt hd.le
  have e : ∀ a b c d, deWitt m a b c d *
      (adjugate m b a / (2 * volume m) * (adjugate m d c / (2 * volume m))) =
      (m a c * m b d + m a d * m b c - m a b * m c d) * adjugate m b a * adjugate m d c /
        (8 * volume m ^ 3) := by
    intro a b c d; unfold deWitt; field_simp; ring
  simp_rw [e, ← Finset.sum_div]
  rw [P1 m hs, ← hv2]
  field_simp

theorem S2 (m : Matrix (Fin 3) (Fin 3) ℝ) (hs : ∀ i j, m i j = m j i) (hd : 0 < m.det) :
    ∑ a, ∑ b, ∑ c, ∑ d, deWitt m a b c d *
      ((Cf m a b c d * (2 * volume m) - adjugate m d c * (2 * (adjugate m b a /
        (2 * volume m)))) / (2 * volume m) ^ 2) = -21 / 8 := by
  have hv : 0 < volume m := Real.sqrt_pos.2 hd
  have hv2 : volume m ^ 2 = m.det := Real.sq_sqrt hd.le
  have e : ∀ a b c d, deWitt m a b c d *
      ((Cf m a b c d * (2 * volume m) - adjugate m d c * (2 * (adjugate m b a /
        (2 * volume m)))) / (2 * volume m) ^ 2) =
      (m a c * m b d + m a d * m b c - m a b * m c d) * Cf m a b c d / (4 * volume m ^ 2) -
      (m a c * m b d + m a d * m b c - m a b * m c d) * adjugate m b a * adjugate m d c /
        (8 * volume m ^ 4) := by
    intro a b c d; unfold deWitt; field_simp; ring
  simp_rw [e, Finset.sum_sub_distrib, ← Finset.sum_div]
  rw [P1 m hs, P2 m hs, ← hv2]
  field_simp; ring

theorem kvs_main {X : Type*} [Fintype X] [DecidableEq X] (x₀ : X)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (h : Config X) (hpos : (metricAt h x₀).PosDef) :
    kinetic (fun h' => f (volume (metricAt h' x₀))) h x₀ =
      -(3 / 8 : ℂ) * ((volume (metricAt h x₀) : ℂ) *
          iteratedDeriv 2 f (volume (metricAt h x₀)) +
        7 * deriv f (volume (metricAt h x₀))) := by
  have hd : 0 < (metricAt h x₀).det := hpos.det_pos
  have hs : ∀ i j, metricAt h x₀ i j = metricAt h x₀ j i := fun i j => by
    simpa using hpos.1.apply j i
  simp only [kinetic, step2 f hf x₀ _ _ _ _ h hd]
  rw [sum_split, S1 _ hs hd, S2 _ hs hd]
  push_cast; ring

end

end WheelerDeWittSuperspace

open WheelerDeWittSuperspace

theorem solution {X : Type*} [Fintype X] [DecidableEq X] (x₀ : X)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 2 f) (h : Config X) (hpos : (metricAt h x₀).PosDef) :
    kinetic (fun h' => f (volume (metricAt h' x₀))) h x₀ =
      -(3 / 8 : ℂ) * ((volume (metricAt h x₀) : ℂ) *
          iteratedDeriv 2 f (volume (metricAt h x₀)) +
        7 * deriv f (volume (metricAt h x₀))) :=
  kvs_main x₀ f hf h hpos
