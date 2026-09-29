-- Prove2me | solution 1 for TongEM.plane_wave_maxwell
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T04:10:26.168541+00:00
-- url     : https://prove2.me/submissions/4b9cd887-9e29-4c97-8340-dc5e52b2b6a7

import Definitions.Def_TongEM_wave_ops

open TongEM Larmor

namespace PWAux

/-- A field depending only on the first coordinate. -/
lemma partialDeriv_field (f : Fin 3 → ℝ → ℝ) (hf : ∀ i, Differentiable ℝ (f i)) (y : Vec) (j i : Fin 3) :
    partialDeriv (fun y : Vec => (!₂[f 0 (y 0), f 1 (y 0), f 2 (y 0)] : Vec)) j i y =
      (EuclideanSpace.single j (1 : ℝ) : Vec) 0 * deriv (f i) (y 0) := by
  unfold partialDeriv
  have hproj : HasFDerivAt (fun y : Vec => y 0) (EuclideanSpace.proj (0 : Fin 3) : Vec →L[ℝ] ℝ) y := by
    rw [show (fun y : Vec => y 0) = ⇑(EuclideanSpace.proj (0 : Fin 3) : Vec →L[ℝ] ℝ) from by
      funext z; simp]
    exact (EuclideanSpace.proj (0 : Fin 3) : Vec →L[ℝ] ℝ).hasFDerivAt
  have hcomp : ∀ k, HasFDerivAt (fun y : Vec => f k (y 0))
      (deriv (f k) (y 0) • (EuclideanSpace.proj (0 : Fin 3) : Vec →L[ℝ] ℝ)) y :=
    fun k => ((hf k) (y 0)).hasDerivAt.comp_hasFDerivAt y hproj
  have hpi : HasFDerivAt (fun y : Vec => ![f 0 (y 0), f 1 (y 0), f 2 (y 0)])
      (ContinuousLinearMap.pi fun k => deriv (f k) (y 0) • (EuclideanSpace.proj (0 : Fin 3) : Vec →L[ℝ] ℝ)) y := by
    rw [hasFDerivAt_pi]
    intro k
    fin_cases k
    · exact hcomp 0
    · exact hcomp 1
    · exact hcomp 2
  have hvec : HasFDerivAt (fun y : Vec => (!₂[f 0 (y 0), f 1 (y 0), f 2 (y 0)] : Vec)) _ y :=
    (PiLp.hasFDerivAt_toLp (p := 2) (𝕜 := ℝ) _).comp y hpi
  rw [hvec.fderiv]
  simp [mul_comm]

/-- Time derivative of a field depending only on time (at a fixed point). -/
lemma deriv_field (g : Fin 3 → ℝ → ℝ) (hg : ∀ i, Differentiable ℝ (g i)) (t : ℝ) :
    deriv (fun s => (!₂[g 0 s, g 1 s, g 2 s] : Vec)) t = !₂[deriv (g 0) t, deriv (g 1) t, deriv (g 2) t] := by
  have hpi : HasDerivAt (fun s => ![g 0 s, g 1 s, g 2 s]) ![deriv (g 0) t, deriv (g 1) t, deriv (g 2) t] t := by
    rw [hasDerivAt_pi]
    intro k
    fin_cases k
    · exact ((hg 0) t).hasDerivAt
    · exact ((hg 1) t).hasDerivAt
    · exact ((hg 2) t).hasDerivAt
  exact ((PiLp.hasFDerivAt_toLp (p := 2) (𝕜 := ℝ) _).comp_hasDerivAt t hpi).deriv

end PWAux

open PWAux in
theorem solution (mu0 eps0 c E0 k omega : ℝ) (hmu0 : 0 < mu0) (heps0 : 0 < eps0)
    (hc : c = Real.sqrt (1 / (mu0 * eps0))) (hdisp : omega = c * k) :
    IsMaxwell eps0 c (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : Vec))
      (fun t x => !₂[0, E0 * Real.sin (k * x 0 - omega * t), 0])
      (fun t x => !₂[0, 0, (E0 / c) * Real.sin (k * x 0 - omega * t)]) := by
  have hc0 : c ≠ 0 := by rw [hc]; exact (Real.sqrt_pos.mpr (by positivity)).ne'
  -- spatial profiles
  set fE : ℝ → Fin 3 → ℝ → ℝ := fun t => ![fun _ => 0, fun z => E0 * Real.sin (k * z - omega * t), fun _ => 0]
  set fB : ℝ → Fin 3 → ℝ → ℝ := fun t => ![fun _ => 0, fun _ => 0, fun z => (E0 / c) * Real.sin (k * z - omega * t)]
  have hfE : ∀ t i, Differentiable ℝ (fE t i) := by
    intro t i; fin_cases i <;> simp [fE] <;> fun_prop
  have hfB : ∀ t i, Differentiable ℝ (fB t i) := by
    intro t i; fin_cases i <;> simp [fB] <;> fun_prop
  have hE : ∀ t, (fun x : Vec => (!₂[0, E0 * Real.sin (k * x 0 - omega * t), 0] : Vec)) =
      fun y : Vec => (!₂[fE t 0 (y 0), fE t 1 (y 0), fE t 2 (y 0)] : Vec) := by
    intro t; funext y; simp [fE]
  have hB : ∀ t, (fun x : Vec => (!₂[0, 0, (E0 / c) * Real.sin (k * x 0 - omega * t)] : Vec)) =
      fun y : Vec => (!₂[fB t 0 (y 0), fB t 1 (y 0), fB t 2 (y 0)] : Vec) := by
    intro t; funext y; simp [fB]
  have dsin : ∀ (a b z : ℝ), deriv (fun z => a * Real.sin (k * z - b)) z = a * (Real.cos (k * z - b) * k) := by
    intro a b z
    have := (((hasDerivAt_id z).const_mul k).sub_const b).sin.const_mul a
    simpa using this.deriv
  have dsint : ∀ (a z s : ℝ), deriv (fun s => a * Real.sin (k * z - omega * s)) s =
      a * (Real.cos (k * z - omega * s) * (-omega)) := by
    intro a z s
    have := (((hasDerivAt_id s).const_mul omega).const_sub (k * z)).sin.const_mul a
    simpa using this.deriv
  have dsin2 : ∀ (a b z : ℝ), deriv (fun s => Real.sin (-(a * s) + b)) z =
      Real.cos (-(a * z) + b) * (-a) := by
    intro a b z
    have := (((hasDerivAt_id z).const_mul a).neg.add_const b).sin
    simpa using this.deriv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t x
    simp only
    rw [hE t]
    simp only [divg, Fin.sum_univ_three, partialDeriv_field _ (hfE t)]
    simp [fE]
  · intro t x
    simp only
    rw [hB t]
    simp only [divg, Fin.sum_univ_three, partialDeriv_field _ (hfB t)]
    simp [fB]
  · intro t x
    simp only
    rw [hE t]
    have htd : deriv (fun s => (!₂[0, 0, (E0 / c) * Real.sin (k * x 0 - omega * s)] : Vec)) t =
        !₂[0, 0, (E0 / c) * (Real.cos (k * x 0 - omega * t) * (-omega))] := by
      have := deriv_field (fun i => ![fun _ => (0:ℝ), fun _ => 0,
        fun s => (E0 / c) * Real.sin (k * x 0 - omega * s)] i)
        (by intro i; fin_cases i <;> simp <;> fun_prop) t
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, deriv_const] at this
      rw [this, dsint]
    rw [htd]
    simp only [curl, partialDeriv_field _ (hfE t)]
    ext i; fin_cases i <;> simp [fE, dsin, hdisp] <;> field_simp <;> ring
  · intro t x
    simp only
    rw [hB t]
    have htd : deriv (fun s => (!₂[0, E0 * Real.sin (k * x 0 - omega * s), 0] : Vec)) t =
        !₂[0, E0 * (Real.cos (k * x 0 - omega * t) * (-omega)), 0] := by
      have := deriv_field (fun i => ![fun _ => (0:ℝ),
        fun s => E0 * Real.sin (k * x 0 - omega * s), fun _ => 0] i)
        (by intro i; fin_cases i <;> simp <;> fun_prop) t
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, deriv_const] at this
      rw [this, dsint]
    rw [htd]
    simp only [curl, partialDeriv_field _ (hfB t)]
    ext i; fin_cases i <;> simp [fB, dsin, hdisp] <;> field_simp <;> ring
