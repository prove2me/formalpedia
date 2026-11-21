-- Prove2me | solution 1 for RiemannMasullo.norm_quasiCharacter_eq_rpow_abscissa
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:12:51.670915+00:00
-- url     : https://prove2.me/submissions/dc4a670a-515a-43d7-92e0-fb5cf64e48c9

-- New proof of the statement in mccorvie/riemann-masullo, Apache-2.0.
-- https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/Ch03_IdelicZeta/Sec1.lean#L115-L119
import Mathlib
import Theorems.Thm_RiemannMasullo_additiveCharacter_proportional_of_slab
import Definitions.Def_RiemannMasullo_QuasiCharacterAbscissa

open RiemannMasullo Function Topology
open scoped NNReal
variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →* ℝ≥0ˣ)
local notation "modℝ" => fun g => ((m g : ℝ≥0) : ℝ)

theorem solution [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (hm : IsProperMap m) (hne : ∃ g, m g ≠ 1)
    (c : QuasiCharacter G) (g : G) :
    ‖c g‖ = (modℝ g) ^ quasiCharacterAbscissa m hm hne c := by
  let M : G →* ℝ := NNReal.toRealHom.toMonoidHom.comp ((Units.coeHom ℝ≥0).comp m)
  have hp (x : G) : 0 < M x := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m x).ne_zero)
  have hc (x : G) : c x ≠ 0 := ((Group.isUnit x).map c).ne_zero
  let a : Additive G →+ ℝ :=
    { toFun := fun x ↦ Real.log (M x.toMul)
      map_zero' := by simp
      map_add' := fun x y ↦ by
        change Real.log (M (x.toMul * y.toMul)) = _
        rw [map_mul, Real.log_mul (hp _).ne' (hp _).ne'] }
  let b : Additive G →+ ℝ :=
    { toFun := fun x ↦ Real.log ‖c x.toMul‖
      map_zero' := by simp
      map_add' := fun x y ↦ by
        change Real.log ‖c (x.toMul * y.toMul)‖ = _
        rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (hc _))
          (norm_ne_zero_iff.mpr (hc _))] }
  let e (r : ℝ) : ℝ≥0ˣ := Units.mk0 (⟨Real.exp r, (Real.exp_pos r).le⟩ : ℝ≥0)
    (ne_of_gt (NNReal.coe_pos.mp (Real.exp_pos r)))
  have he : Continuous e := Units.isEmbedding_val₀.continuous_iff.mpr
    (Real.continuous_exp.subtype_mk _)
  have hb : Continuous (fun x : G ↦ |Real.log ‖c x‖|) :=
    (c.continuous.norm.log fun x ↦ norm_ne_zero_iff.mpr (hc x)).abs
  have hs (u : Additive G) (hu : 0 < a u) (x : Additive G) :
      b x = a x * (b u / a u) := by
    have hk := hm.isCompact_preimage (isCompact_Icc.image he :
      IsCompact (e '' Set.Icc 0 (a u)))
    obtain ⟨C, hC⟩ := hk.bddAbove_image hb.continuousOn
    apply additiveCharacter_proportional_of_slab a b u hu C _ x
    intro y hy hy'
    apply hC
    refine ⟨y.toMul, ⟨a y, ⟨hy, hy'⟩, ?_⟩, rfl⟩
    apply Units.ext
    apply NNReal.eq
    exact Real.exp_log (hp y.toMul)
  let v := Additive.ofMul hne.choose
  have hv : a v ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (hp _) fun h ↦
    hne.choose_spec (Units.val_inj.mp (NNReal.coe_inj.mp h))
  have h : b (Additive.ofMul g) = a (Additive.ofMul g) * (b v / a v) := by
    rcases lt_or_gt_of_ne hv with hn | hp'
    · simpa using hs (-v) (by simpa using hn) (Additive.ofMul g)
    · exact hs v hp' _
  change Real.log ‖c g‖ = Real.log (M g) * quasiCharacterAbscissa m hm hne c at h
  change ‖c g‖ = (M g) ^ quasiCharacterAbscissa m hm hne c
  rw [Real.rpow_def_of_pos (hp g), ← h, Real.exp_log (norm_pos_iff.mpr (hc g))]
