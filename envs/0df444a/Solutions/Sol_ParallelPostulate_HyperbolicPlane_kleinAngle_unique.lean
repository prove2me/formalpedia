-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.kleinAngle_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:38.002335+00:00
-- url     : https://prove2.me/submissions/8d6d078b-17a7-431e-b9c6-3de95b61f2cd

module
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Definitions.Def_LeanPool_ParallelPostulate_Hilbert
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_LeanPool_ParallelPostulate
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_kleinAngle_centre
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_shift_kleinAngle
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_rot_kleinAngle
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
open Real
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ : ℝ} (hκ : κ ≤ 0) (θ : ℝ × ℝ → ℝ × ℝ → ℝ × ℝ → ℝ)
    (hshift : ∀ a w : ℝ, w ^ 2 = 1 + κ * a ^ 2 → 0 < w → ∀ P A B : ℝ × ℝ,
      P ∈ plane κ → A ∈ plane κ → B ∈ plane κ →
        θ (shift κ a w P) (shift κ a w A) (shift κ a w B) = θ P A B)
    (hrot : ∀ c s : ℝ, c ^ 2 + s ^ 2 = 1 → ∀ P A B : ℝ × ℝ,
      P ∈ plane κ → A ∈ plane κ → B ∈ plane κ →
        θ (rot c s P) (rot c s A) (rot c s B) = θ P A B)
    (hcentre : ∀ A B : ℝ × ℝ, A ∈ plane κ → B ∈ plane κ →
      θ (0, 0) A B
        = InnerProductGeometry.angle (!₂[A.1, A.2] : EuclideanSpace ℝ (Fin 2)) !₂[B.1, B.2])
    {P A B : ℝ × ℝ} (hP : P ∈ plane κ) (hA : A ∈ plane κ) (hB : B ∈ plane κ) :
    θ P A B = kleinAngle κ P A B := by
  obtain ⟨c, s, a, w, hcs, hw, hw0, hPc⟩ := exists_motion_to_centre hP
  have hr : ∀ X : ℝ × ℝ, X ∈ plane κ → rot c s X ∈ plane κ :=
    fun X hX => (rot_mem_plane hcs).mpr hX
  have hm : ∀ X : ℝ × ℝ, X ∈ plane κ → shift κ a w (rot c s X) ∈ plane κ :=
    fun X hX => shift_mem_plane hκ hw hw0.ne' (hr X hX)
  calc θ P A B = θ (rot c s P) (rot c s A) (rot c s B) := (hrot c s hcs P A B hP hA hB).symm
    _ = θ (shift κ a w (rot c s P)) (shift κ a w (rot c s A)) (shift κ a w (rot c s B)) :=
      (hshift a w hw hw0 _ _ _ (hr P hP) (hr A hA) (hr B hB)).symm
    _ = θ (0, 0) (shift κ a w (rot c s A)) (shift κ a w (rot c s B)) := by rw [hPc]
    _ = kleinAngle κ (0, 0) (shift κ a w (rot c s A)) (shift κ a w (rot c s B)) := by
      rw [hcentre _ _ (hm A hA) (hm B hB), kleinAngle_centre]
    _ = kleinAngle κ (shift κ a w (rot c s P)) (shift κ a w (rot c s A))
          (shift κ a w (rot c s B)) := by rw [hPc]
    _ = kleinAngle κ (rot c s P) (rot c s A) (rot c s B) :=
      shift_kleinAngle hκ hw hw0.ne' (hr P hP) (hr A hA) (hr B hB)
    _ = kleinAngle κ P A B := rot_kleinAngle hcs κ P A B
end ParallelPostulate.HyperbolicPlane
