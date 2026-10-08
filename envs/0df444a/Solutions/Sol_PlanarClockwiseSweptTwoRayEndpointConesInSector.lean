-- Prove2me | solution 1 for PlanarClockwiseSweptTwoRayEndpointConesInSector
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T22:33:04.99674+00:00
-- url     : https://prove2.me/submissions/c116d284-06c2-43fb-8974-2b797203446e

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Definitions.Def_PlanarRot90
import Theorems.Thm_PlanarClockwiseTwoRayEndpointConesInSector
import Theorems.Thm_PlanarRot90CoefficientUniqueness
import Theorems.Thm_PlanarRot90Decomposition
import Theorems.Thm_PlanarRot90Norm
import Theorems.Thm_PlanarRot90Orthogonal

open Classical
noncomputable section
set_option maxHeartbeats 1200000

theorem solution
    (p base other : EuclideanSpace ℝ (Fin 2)) (rho c s : ℝ)
    (hrho : 0 < rho) (hbase : base ≠ 0) (hother : other ≠ 0)
    (hnot_pos_ray : s ≠ 0 ∨ c < 0)
    (hother_eq : other = c • base - s • PlanarRot90 base) :
    let baseChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • base + z 1 • PlanarRot90 base
    let otherChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • other + z 1 • PlanarRot90 other
    let sector : Set (EuclideanSpace ℝ (Fin 2)) :=
      if 0 < s then
        baseChart ''
          {z | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2 ∧
            z 1 < 0 ∧ 0 < c * z 1 + s * z 0}
      else
        if s < 0 then
          baseChart ''
            {z | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2 ∧
              (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)}
        else
          baseChart ''
            {z | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2 ∧ z 1 < 0}
    IsOpen sector ∧ IsConnected sector ∧
      ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
        baseChart ''
            {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖base‖) ^ 2 ∧
              -K * z 0 < z 1 ∧ z 1 < 0} ⊆ sector ∧
          otherChart ''
            {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖other‖) ^ 2 ∧
              0 < z 1 ∧ z 1 < K * z 0} ⊆ sector := by
  by_cases hspos : 0 < s
  · simpa [hspos] using
      PlanarClockwiseTwoRayEndpointConesInSector p base other rho c s
        hrho hbase hother hspos hother_eq
  · have hbase_norm_pos : 0 < ‖base‖ := norm_pos_iff.mpr hbase
    have hother_norm_pos : 0 < ‖other‖ := norm_pos_iff.mpr hother
    have hR_pos : 0 < rho / ‖base‖ := div_pos hrho hbase_norm_pos
    have hnormsq_coord (z : EuclideanSpace ℝ (Fin 2)) :
        z 0 ^ 2 + z 1 ^ 2 = ‖z‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
      simp
    have hdisk_eq :
        {z : EuclideanSpace ℝ (Fin 2) | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2} =
          Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (rho / ‖base‖) := by
      ext z
      rw [Set.mem_setOf_eq, Metric.mem_ball]
      simp [hnormsq_coord z, (sq_lt_sq₀ (norm_nonneg z) (le_of_lt hR_pos))]
    have chart_image_open (p d : EuclideanSpace ℝ (Fin 2)) (hd : d ≠ 0)
        (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : IsOpen S) :
        IsOpen ((fun z : EuclideanSpace ℝ (Fin 2) =>
          p + z 0 • d + z 1 • PlanarRot90 d) '' S) := by
      let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
        fun z => p + z 0 • d + z 1 • PlanarRot90 d
      let invCoord : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
        fun q => WithLp.toLp 2 (fun i : Fin 2 =>
          if i = 0 then inner ℝ (q - p) d / (‖d‖ ^ 2)
          else inner ℝ (q - p) (PlanarRot90 d) / (‖d‖ ^ 2))
      have hinv_cont : Continuous invCoord := by
        have hplain : Continuous fun q : EuclideanSpace ℝ (Fin 2) =>
            (fun i : Fin 2 =>
              if i = 0 then inner ℝ (q - p) d / (‖d‖ ^ 2)
              else inner ℝ (q - p) (PlanarRot90 d) / (‖d‖ ^ 2)) := by
          apply continuous_pi
          intro i
          by_cases hi : i = 0
          · simp [hi]
            fun_prop
          · simp [hi]
            fun_prop
        exact (PiLp.continuous_toLp (p := (2 : ENNReal))
          (β := fun _ : Fin 2 => ℝ)).comp hplain
      have hleft_inv :
          ∀ z : EuclideanSpace ℝ (Fin 2), invCoord (chart z) = z := by
        intro z
        have hrepz :
            chart z - p = z 0 • d + z 1 • PlanarRot90 d := by
          dsimp [chart]
          abel
        have hcoeff :=
          PlanarRot90CoefficientUniqueness (d := d) (v := chart z - p)
            hd hrepz
        apply PiLp.ext
        intro i
        fin_cases i
        · simpa [invCoord] using hcoeff.1.symm
        · simpa [invCoord] using hcoeff.2.symm
      have hright_inv :
          ∀ q : EuclideanSpace ℝ (Fin 2), chart (invCoord q) = q := by
        intro q
        have hdecomp :
            q - p = (invCoord q) 0 • d + (invCoord q) 1 • PlanarRot90 d := by
          simpa [invCoord] using PlanarRot90Decomposition d (q - p) hd
        calc
          chart (invCoord q) =
              p + ((invCoord q) 0 • d + (invCoord q) 1 • PlanarRot90 d) := by
            dsimp [chart]
            abel
          _ = p + (q - p) := by rw [← hdecomp]
          _ = q := by abel
      have himage_eq_preimage (T : Set (EuclideanSpace ℝ (Fin 2))) :
          chart '' T = invCoord ⁻¹' T := by
        ext q
        constructor
        · rintro ⟨z, hz, rfl⟩
          simpa [hleft_inv z] using hz
        · intro hq
          exact ⟨invCoord q, hq, hright_inv q⟩
      change IsOpen (chart '' S)
      rw [himage_eq_preimage S]
      exact hS.preimage hinv_cont
    have chart_image_connected (p d : EuclideanSpace ℝ (Fin 2))
        (S : Set (EuclideanSpace ℝ (Fin 2))) (hS : IsConnected S) :
        IsConnected ((fun z : EuclideanSpace ℝ (Fin 2) =>
          p + z 0 • d + z 1 • PlanarRot90 d) '' S) := by
      have hchart_cont : Continuous fun z : EuclideanSpace ℝ (Fin 2) =>
          p + z 0 • d + z 1 • PlanarRot90 d := by
        fun_prop
      exact hS.image _ hchart_cont.continuousOn
    have hnorm_combo (x y : ℝ) :
        ‖x • base + y • PlanarRot90 base‖ ^ 2 =
          (x ^ 2 + y ^ 2) * ‖base‖ ^ 2 := by
      have horth : inner ℝ (x • base) (y • PlanarRot90 base) = 0 := by
        rw [inner_smul_left, inner_smul_right, PlanarRot90Orthogonal]
        ring
      have horth' : inner ℝ (y • PlanarRot90 base) (x • base) = 0 := by
        rw [real_inner_comm, horth]
      rw [← real_inner_self_eq_norm_sq]
      rw [inner_add_left, inner_add_right, inner_add_right, horth, horth']
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      rw [norm_smul, norm_smul, PlanarRot90Norm]
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      nlinarith [sq_abs x, sq_abs y]
    have hother_norm_sq : ‖other‖ ^ 2 = (c ^ 2 + s ^ 2) * ‖base‖ ^ 2 := by
      calc
        ‖other‖ ^ 2 = ‖c • base + (-s) • PlanarRot90 base‖ ^ 2 := by
          rw [hother_eq]
          simp [sub_eq_add_neg, neg_smul]
        _ = (c ^ 2 + (-s) ^ 2) * ‖base‖ ^ 2 := hnorm_combo c (-s)
        _ = (c ^ 2 + s ^ 2) * ‖base‖ ^ 2 := by ring
    have hsmall_radius :
        (rho / 2 / ‖base‖) ^ 2 < (rho / ‖base‖) ^ 2 := by
      have hhalf_pos : 0 < rho / 2 := by linarith
      have hhalf_lt : rho / 2 < rho := by linarith
      have hdiv_lt : rho / 2 / ‖base‖ < rho / ‖base‖ :=
        div_lt_div_of_pos_right hhalf_lt hbase_norm_pos
      exact (sq_lt_sq₀ (le_of_lt (div_pos hhalf_pos hbase_norm_pos))
        (le_of_lt hR_pos)).mpr hdiv_lt
    by_cases hsneg : s < 0
    · let baseChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
        fun z => p + z 0 • base + z 1 • PlanarRot90 base
      let otherChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
        fun z => p + z 0 • other + z 1 • PlanarRot90 other
      let coordSet : Set (EuclideanSpace ℝ (Fin 2)) :=
        {z | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2 ∧
          (z 1 < 0 ∨ 0 < c * z 1 + s * z 0)}
      let lower : Set (EuclideanSpace ℝ (Fin 2)) :=
        {z | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2 ∧ z 1 < 0}
      let cap : Set (EuclideanSpace ℝ (Fin 2)) :=
        {z | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2 ∧
          0 < c * z 1 + s * z 0}
      have hcoord_eq : coordSet = lower ∪ cap := by
        ext z
        constructor
        · intro hz
          rcases hz with ⟨hzdisk, hzy | hzlin⟩
          · exact Or.inl ⟨hzdisk, hzy⟩
          · exact Or.inr ⟨hzdisk, hzlin⟩
        · intro hz
          rcases hz with hz | hz
          · exact ⟨hz.1, Or.inl hz.2⟩
          · exact ⟨hz.1, Or.inr hz.2⟩
      have hdisk_open :
          IsOpen {z : EuclideanSpace ℝ (Fin 2) |
            z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2} := by
        exact isOpen_lt (by fun_prop) continuous_const
      have hyneg_open : IsOpen {z : EuclideanSpace ℝ (Fin 2) | z 1 < 0} := by
        exact isOpen_lt (by fun_prop) continuous_const
      have hboundary_open :
          IsOpen {z : EuclideanSpace ℝ (Fin 2) | 0 < c * z 1 + s * z 0} := by
        exact isOpen_lt continuous_const (by fun_prop)
      have hlower_open : IsOpen lower := by
        simpa [lower, Set.inter_def] using hdisk_open.inter hyneg_open
      have hcap_open : IsOpen cap := by
        simpa [cap, Set.inter_def] using hdisk_open.inter hboundary_open
      have hcoord_open : IsOpen coordSet := by
        rw [hcoord_eq]
        exact hlower_open.union hcap_open
      have hdisk_conv :
          Convex ℝ {z : EuclideanSpace ℝ (Fin 2) |
            z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2} := by
        simpa [hdisk_eq] using
          convex_ball (0 : EuclideanSpace ℝ (Fin 2)) (rho / ‖base‖)
      have hyneg_conv :
          Convex ℝ {z : EuclideanSpace ℝ (Fin 2) | z 1 < 0} := by
        refine convex_halfSpace_lt ?_ 0
        exact IsLinearMap.mk (by intro x y; simp) (by intro a x; simp)
      have hboundary_conv :
          Convex ℝ {z : EuclideanSpace ℝ (Fin 2) | 0 < c * z 1 + s * z 0} := by
        refine convex_halfSpace_gt ?_ 0
        refine IsLinearMap.mk ?_ ?_
        · intro x y
          simp
          ring
        · intro a x
          simp
          ring
      have hlower_conv : Convex ℝ lower := by
        simpa [lower, Set.inter_def] using hdisk_conv.inter hyneg_conv
      have hcap_conv : Convex ℝ cap := by
        simpa [cap, Set.inter_def] using hdisk_conv.inter hboundary_conv
      have hneg_s_pos : 0 < -s := neg_pos.mpr hsneg
      let M : ℝ := (|c| + 1) / (-s) + 1
      have hM_pos : 0 < M := by
        have hnum_pos : 0 < |c| + 1 := by
          exact add_pos_of_nonneg_of_pos (abs_nonneg c) zero_lt_one
        have hdiv_pos : 0 < (|c| + 1) / (-s) := div_pos hnum_pos hneg_s_pos
        dsimp [M]
        linarith
      have hMlarge : |c| + 1 < (-s) * M := by
        have hM_eq : (-s) * M = |c| + 1 + (-s) := by
          dsimp [M]
          rw [mul_add, mul_one, mul_comm (-s) ((|c| + 1) / (-s))]
          rw [div_mul_cancel₀ (|c| + 1) (ne_of_gt hneg_s_pos)]
        rw [hM_eq]
        linarith
      have hden_pos : 0 < 2 * (M + 1) := by nlinarith
      let eps : ℝ := (rho / ‖base‖) / (2 * (M + 1))
      have heps_pos : 0 < eps := div_pos hR_pos hden_pos
      let zI : EuclideanSpace ℝ (Fin 2) :=
        WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then -M * eps else -eps)
      have hzI_disk : zI 0 ^ 2 + zI 1 ^ 2 < (rho / ‖base‖) ^ 2 := by
        have hden_ne : 2 * (M + 1) ≠ 0 := ne_of_gt hden_pos
        dsimp [zI, eps]
        simp
        field_simp [hden_ne]
        nlinarith [sq_nonneg M, mul_pos hR_pos hR_pos, hM_pos]
      have hzI_yneg : zI 1 < 0 := by
        dsimp [zI]
        simp [heps_pos]
      have hzI_boundary : 0 < c * zI 1 + s * zI 0 := by
        have hlinear : 0 < -c - s * M := by
          have hc_le_abs : c ≤ |c| := le_abs_self c
          nlinarith [hMlarge, hc_le_abs]
        have hprod : 0 < eps * (-c - s * M) := mul_pos heps_pos hlinear
        dsimp [zI]
        simp
        nlinarith
      have hinter : (lower ∩ cap).Nonempty := by
        refine ⟨zI, ?_⟩
        exact ⟨⟨hzI_disk, hzI_yneg⟩, ⟨hzI_disk, hzI_boundary⟩⟩
      have hlower_conn : IsConnected lower :=
        hlower_conv.isConnected ⟨zI, hzI_disk, hzI_yneg⟩
      have hcap_conn : IsConnected cap :=
        hcap_conv.isConnected ⟨zI, hzI_disk, hzI_boundary⟩
      have hcoord_conn : IsConnected coordSet := by
        rw [hcoord_eq]
        exact IsConnected.union hinter hlower_conn hcap_conn
      have hsector_open : IsOpen (baseChart '' coordSet) := by
        simpa [baseChart] using chart_image_open p base hbase coordSet hcoord_open
      have hsector_conn : IsConnected (baseChart '' coordSet) := by
        simpa [baseChart] using chart_image_connected p base coordSet hcoord_conn
      have hcs_pos : 0 < c ^ 2 + s ^ 2 := by
        nlinarith [sq_nonneg c, sq_pos_of_ne_zero (ne_of_lt hsneg)]
      have hresult :
          IsOpen (baseChart '' coordSet) ∧ IsConnected (baseChart '' coordSet) ∧
            ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
              baseChart ''
                  {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖base‖) ^ 2 ∧
                    -K * z 0 < z 1 ∧ z 1 < 0} ⊆ baseChart '' coordSet ∧
                otherChart ''
                  {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖other‖) ^ 2 ∧
                    0 < z 1 ∧ z 1 < K * z 0} ⊆ baseChart '' coordSet := by
        refine ⟨hsector_open, hsector_conn, ?_⟩
        refine ⟨rho / 2, 1, by linarith, by norm_num, ?_, ?_⟩
        · intro q hq
          rcases hq with ⟨z, hz, rfl⟩
          rcases hz with ⟨hzx, hzrad, hzy_low, hzy_neg⟩
          refine ⟨z, ?_, rfl⟩
          exact ⟨lt_trans hzrad hsmall_radius, Or.inl hzy_neg⟩
        · intro q hq
          rcases hq with ⟨z, hz, rfl⟩
          rcases hz with ⟨hzu, hzrad, hzvpos, hzvupper⟩
          let w : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i : Fin 2 =>
            if i = 0 then z 0 * c + z 1 * s else -z 0 * s + z 1 * c)
          refine ⟨w, ?_, ?_⟩
          · refine ⟨?_, ?_⟩
            · have hw_sq :
                  w 0 ^ 2 + w 1 ^ 2 = (z 0 ^ 2 + z 1 ^ 2) * (c ^ 2 + s ^ 2) := by
                simp [w]
                ring
              have hscale_eq :
                  (rho / 2 / ‖other‖) ^ 2 * (c ^ 2 + s ^ 2) =
                    (rho / 2 / ‖base‖) ^ 2 := by
                have hno_ne : ‖other‖ ≠ 0 := ne_of_gt hother_norm_pos
                have hnb_ne : ‖base‖ ≠ 0 := ne_of_gt hbase_norm_pos
                have hcs_ne : c ^ 2 + s ^ 2 ≠ 0 := ne_of_gt hcs_pos
                field_simp [hno_ne, hnb_ne, hcs_ne] at hother_norm_sq ⊢
                nlinarith
              have hscaled :
                  (z 0 ^ 2 + z 1 ^ 2) * (c ^ 2 + s ^ 2) <
                    (rho / 2 / ‖base‖) ^ 2 := by
                have hmul := mul_lt_mul_of_pos_right hzrad hcs_pos
                simpa [hscale_eq] using hmul
              rw [hw_sq]
              exact lt_trans hscaled hsmall_radius
            · by_cases hwneg : w 1 < 0
              · exact Or.inl hwneg
              · exact Or.inr (by
                  have hwlin :
                      c * w 1 + s * w 0 = z 1 * (c ^ 2 + s ^ 2) := by
                    simp [w]
                    ring
                  rw [hwlin]
                  exact mul_pos hzvpos hcs_pos)
          · apply PiLp.ext
            intro k
            fin_cases k <;>
              simp [w, otherChart, baseChart, hother_eq, PlanarRot90] <;>
              ring
      simpa [baseChart, otherChart, coordSet, hspos, hsneg] using hresult
    · have hs_eq : s = 0 := le_antisymm (not_lt.mp hspos) (not_lt.mp hsneg)
      have hcneg : c < 0 := by
        rcases hnot_pos_ray with hsne | hc
        · exact False.elim (hsne hs_eq)
        · exact hc
      let baseChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
        fun z => p + z 0 • base + z 1 • PlanarRot90 base
      let otherChart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
        fun z => p + z 0 • other + z 1 • PlanarRot90 other
      let coordSet : Set (EuclideanSpace ℝ (Fin 2)) :=
        {z | z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2 ∧ z 1 < 0}
      have hdisk_open :
          IsOpen {z : EuclideanSpace ℝ (Fin 2) |
            z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2} := by
        exact isOpen_lt (by fun_prop) continuous_const
      have hyneg_open : IsOpen {z : EuclideanSpace ℝ (Fin 2) | z 1 < 0} := by
        exact isOpen_lt (by fun_prop) continuous_const
      have hcoord_open : IsOpen coordSet := by
        simpa [coordSet, Set.inter_def] using hdisk_open.inter hyneg_open
      have hdisk_conv :
          Convex ℝ {z : EuclideanSpace ℝ (Fin 2) |
            z 0 ^ 2 + z 1 ^ 2 < (rho / ‖base‖) ^ 2} := by
        simpa [hdisk_eq] using
          convex_ball (0 : EuclideanSpace ℝ (Fin 2)) (rho / ‖base‖)
      have hyneg_conv :
          Convex ℝ {z : EuclideanSpace ℝ (Fin 2) | z 1 < 0} := by
        refine convex_halfSpace_lt ?_ 0
        exact IsLinearMap.mk (by intro x y; simp) (by intro a x; simp)
      have hcoord_conv : Convex ℝ coordSet := by
        simpa [coordSet, Set.inter_def] using hdisk_conv.inter hyneg_conv
      let eps : ℝ := (rho / ‖base‖) / 2
      have heps_pos : 0 < eps := by
        dsimp [eps]
        linarith
      let zI : EuclideanSpace ℝ (Fin 2) :=
        WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then 0 else -eps)
      have hzI_mem : zI ∈ coordSet := by
        refine ⟨?_, ?_⟩
        · dsimp [zI, eps]
          simp
          nlinarith [hR_pos]
        · dsimp [zI]
          simp [heps_pos]
      have hcoord_conn : IsConnected coordSet :=
        hcoord_conv.isConnected ⟨zI, hzI_mem⟩
      have hsector_open : IsOpen (baseChart '' coordSet) := by
        simpa [baseChart] using chart_image_open p base hbase coordSet hcoord_open
      have hsector_conn : IsConnected (baseChart '' coordSet) := by
        simpa [baseChart] using chart_image_connected p base coordSet hcoord_conn
      have hcs_pos : 0 < c ^ 2 + s ^ 2 := by
        nlinarith [sq_pos_of_ne_zero (ne_of_lt hcneg), sq_nonneg s]
      have hresult :
          IsOpen (baseChart '' coordSet) ∧ IsConnected (baseChart '' coordSet) ∧
            ∃ r K : ℝ, 0 < r ∧ 0 < K ∧
              baseChart ''
                  {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖base‖) ^ 2 ∧
                    -K * z 0 < z 1 ∧ z 1 < 0} ⊆ baseChart '' coordSet ∧
                otherChart ''
                  {z | 0 < z 0 ∧ z 0 ^ 2 + z 1 ^ 2 < (r / ‖other‖) ^ 2 ∧
                    0 < z 1 ∧ z 1 < K * z 0} ⊆ baseChart '' coordSet := by
        refine ⟨hsector_open, hsector_conn, ?_⟩
        refine ⟨rho / 2, 1, by linarith, by norm_num, ?_, ?_⟩
        · intro q hq
          rcases hq with ⟨z, hz, rfl⟩
          rcases hz with ⟨hzx, hzrad, hzy_low, hzy_neg⟩
          refine ⟨z, ?_, rfl⟩
          exact ⟨lt_trans hzrad hsmall_radius, hzy_neg⟩
        · intro q hq
          rcases hq with ⟨z, hz, rfl⟩
          rcases hz with ⟨hzu, hzrad, hzvpos, hzvupper⟩
          let w : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i : Fin 2 =>
            if i = 0 then z 0 * c + z 1 * s else -z 0 * s + z 1 * c)
          refine ⟨w, ?_, ?_⟩
          · refine ⟨?_, ?_⟩
            · have hw_sq :
                  w 0 ^ 2 + w 1 ^ 2 = (z 0 ^ 2 + z 1 ^ 2) * (c ^ 2 + s ^ 2) := by
                simp [w]
                ring
              have hscale_eq :
                  (rho / 2 / ‖other‖) ^ 2 * (c ^ 2 + s ^ 2) =
                    (rho / 2 / ‖base‖) ^ 2 := by
                have hno_ne : ‖other‖ ≠ 0 := ne_of_gt hother_norm_pos
                have hnb_ne : ‖base‖ ≠ 0 := ne_of_gt hbase_norm_pos
                have hcs_ne : c ^ 2 + s ^ 2 ≠ 0 := ne_of_gt hcs_pos
                field_simp [hno_ne, hnb_ne, hcs_ne] at hother_norm_sq ⊢
                nlinarith
              have hscaled :
                  (z 0 ^ 2 + z 1 ^ 2) * (c ^ 2 + s ^ 2) <
                    (rho / 2 / ‖base‖) ^ 2 := by
                have hmul := mul_lt_mul_of_pos_right hzrad hcs_pos
                simpa [hscale_eq] using hmul
              rw [hw_sq]
              exact lt_trans hscaled hsmall_radius
            · have hw_y_neg : w 1 < 0 := by
                simp [w, hs_eq]
                exact mul_neg_of_pos_of_neg hzvpos hcneg
              exact hw_y_neg
          · apply PiLp.ext
            intro k
            fin_cases k <;>
              simp [w, otherChart, baseChart, hother_eq, PlanarRot90] <;>
              ring
      simpa [baseChart, otherChart, coordSet, hspos, hsneg, hs_eq] using hresult
