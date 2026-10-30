-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P08.strictTwoGroup_sourceKernel_crossedModule
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:59:25.634875+00:00
-- url     : https://prove2.me/submissions/b64aedfd-3c16-437a-b495-85018f1e4166

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P08
namespace QAlgorithms.Papers.Independent.Bridge50.P08

open Set Filter Topology

open QAlgorithms.Papers.Independent.Renew46.P18

open QAlgorithms.Papers.Independent.Claimed50.P22

open QAlgorithms.Papers.Independent.Next46.P35

universe u v w z

theorem s110b08_comm {G : Type u} {K : Type v} [Group G] [Group K]
    (s t : K →* G) (identity : G →* K)
    (comp : K → K → K) (arrowInv : K → K)
    (h : IsStrictTwoGroup s t identity comp arrowInv) (x k : K)
    (hx : t x = 1) (hk : s k = 1) : x * k = k * x := by
  obtain ⟨-, -, hid, -, -, -, -, -, -, -, hint, -⟩ := h
  have h1x : comp 1 x = x := by
    have := (hid x).1; rwa [hx, map_one] at this
  have hk1 : comp k 1 = k := by
    have := (hid k).2; rwa [hk, map_one] at this
  have e1 := hint x 1 1 k (by rw [hx, map_one]) (by rw [hk, map_one])
  have e2 := hint 1 k x 1 (by rw [hk, map_one]) (by rw [hx, map_one])
  simp only [one_mul, mul_one] at e1 e2
  rw [h1x, hk1] at e1
  rw [h1x, hk1] at e2
  rw [← e1, e2]

end QAlgorithms.Papers.Independent.Bridge50.P08

open QAlgorithms.Papers.Independent.Bridge50.P08
open QAlgorithms.Papers.Independent.Renew46.P18
open QAlgorithms.Papers.Independent.Claimed50.P22
open QAlgorithms.Papers.Independent.Next46.P35

universe u v

theorem solution
    {G : Type u} {K : Type v} [Group G] [Group K]
    (s t : K →* G) (identity : G →* K)
    (comp : K → K → K) (arrowInv : K → K)
    (h : IsStrictTwoGroup s t identity comp arrowInv) :
    IsCrossedModule (t.comp s.ker.subtype)
      (sourceKernelAction s identity (fun g => (h.1 g).1)) := by
  constructor
  · intro g k
    change t (identity g * k.val * (identity g)⁻¹) = g * t k.val * g⁻¹
    simp [(h.1 g).2]
  · intro a k
    apply Subtype.ext
    change identity (t a.val) * k.val * (identity (t a.val))⁻¹ = a.val * k.val * a.val⁻¹
    have ha : s a.val = 1 := a.property
    have hk : s k.val = 1 := k.property
    have hc := s110b08_comm s t identity comp arrowInv h ((identity (t a.val))⁻¹ * a.val) k.val
      (by simp [(h.1 _).2]) hk
    have : a.val * k.val = identity (t a.val) * k.val * (identity (t a.val))⁻¹ * a.val := by
      calc a.val * k.val = identity (t a.val) * (((identity (t a.val))⁻¹ * a.val) * k.val) := by group
        _ = identity (t a.val) * (k.val * ((identity (t a.val))⁻¹ * a.val)) := by rw [hc]
        _ = _ := by group
    rw [this]; group
