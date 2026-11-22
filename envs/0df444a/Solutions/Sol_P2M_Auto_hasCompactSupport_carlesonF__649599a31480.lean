-- Prove2me | solution 1 for P2M_Auto_hasCompactSupport_carlesonF__649599a31480
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:47:03.834806+00:00
-- url     : https://prove2.me/submissions/c149f361-0b68-4fd8-ba1c-fce91bf87094

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_isCompact_carlesonBox
public import Theorems.Thm_P2M_Auto_carlesonF__eq_zero_fe95b4220c40

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution {g : ℝ → ℂ} {L : ℝ} (hg : ∀ x, L < |x| → g x = 0) :
    HasCompactSupport (carlesonF₁ g) :=
  HasCompactSupport.intro (isCompact_carlesonBox L) fun _ hp => carlesonF₁_eq_zero hg hp
end Auto
