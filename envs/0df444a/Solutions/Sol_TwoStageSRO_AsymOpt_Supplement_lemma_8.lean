-- Prove2me | solution 1 for TwoStageSRO.AsymOpt.Supplement.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:12:42.972098+00:00
-- url     : https://prove2.me/submissions/46ec334e-4ddf-47db-ac81-8ef33c6e188f

import Mathlib
import Definitions.Def_CombOpt_MatchingPolytope_IsPolyhedron
import Definitions.Def_TwoStageSRO_AsymOpt_Geometry
import Definitions.Def_TwoStageSRO_AsymOpt_Supplement_PolyGeometry

open Matrix
open scoped ENNReal

open TwoStageSRO
open TwoStageSRO.AsymOpt
open TwoStageSRO.AsymOpt.Supplement

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 39, Lemma 8:
if `T ⊆ Ξ` is a nonempty polyhedron, then `1 ≤ θ^T_Ξ < ∞`.

**Formalization Note** `θ^T_Ξ` is `thetaPoly` (Definition 4, in `EReal`). The appendix's standing
normalization `‖gᵢ‖_* = 1` (p. 33) is the hypothesis `hG`; its other standing assumption, minimality of
the representation of `Ξ`, is not imposed (a disclosed strengthening). A polyhedron is a set
`{x : Ax ≤ b}` (published `CombOpt.MatchingPolytope.IsPolyhedron`). -/
theorem solution {n d r m mt : ℕ} (M : Model n d r m mt) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hG : ∀ k, dualNorm p (M.G k) = 1)
    (T : Set (Fin d → ℝ)) (hTpoly : CombOpt.MatchingPolytope.IsPolyhedron T)
    (hTXi : T ⊆ Xi M) (hTne : T.Nonempty) :
    1 ≤ thetaPoly M p T ∧ thetaPoly M p T < ⊤ := by
      set_option maxHeartbeats 0 in
        classical
        let E := WithLp p (Fin d → ℝ)
        have hlocal (k : ℕ) (a : Fin k → E →L[ℝ] ℝ) (b : Fin k → ℝ)
            (y v : E) (hy : ∀ j, a j y ≤ b j)
            (hv : ∀ j, a j y = b j → a j v ≤ 0) :
            ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ ∀ j, a j (y + t • v) ≤ b j := by
          have he : ∀ᶠ t : ℝ in nhds 0, ∀ j, 0 ≤ t → a j (y + t • v) ≤ b j := by
            rw [Filter.eventually_all]
            intro j
            by_cases hj : a j y = b j
            · exact Filter.Eventually.of_forall fun t ht => by
                simp only [map_add, map_smul, smul_eq_mul]
                nlinarith [hv j hj]
            · have hj' : a j y < b j := lt_of_le_of_ne (hy j) hj
              have hc : Continuous (fun t : ℝ => a j (y + t • v)) := by fun_prop
              filter_upwards [(hc.tendsto 0).eventually_lt_const (by simpa using hj')] with t ht using fun _ => ht.le
          obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp he
          let t := min (ε / 2) (1 / 2 : ℝ)
          refine ⟨t, lt_min (by positivity) (by norm_num), le_trans (min_le_right _ _) (by norm_num), fun j => he ?_ j (le_of_lt (lt_min (by positivity) (by norm_num)))⟩
          rw [Real.dist_eq, sub_zero, abs_of_pos (lt_min (by positivity) (by norm_num))]
          exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hbound (k : ℕ) (a : Fin k → E →L[ℝ] ℝ) (b : Fin k → ℝ)
            (g : E →L[ℝ] ℝ) (c : ℝ)
            (hne : ∃ y : E, (∀ j, a j y ≤ b j) ∧ g y = c) :
            ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, (∀ j, a j x ≤ b j) →
              ∃ y : E, (∀ j, a j y ≤ b j) ∧ g y = c ∧ ‖x - y‖ ≤ C * |g x - c| := by
          let K (J : Finset (Fin k)) : Set E := {v | (∀ j ∈ J, a j v ≤ 0) ∧ g v = 0}
          let S (J : Finset (Fin k)) : Set E :=
            {u | ‖u‖ = 1 ∧ (∀ j ∈ J, a j u ≤ 0) ∧ ∀ v ∈ K J, ‖u‖ ≤ ‖u - v‖}
          have hc (J : Finset (Fin k)) : IsCompact (S J) := by
            apply (isCompact_sphere (0 : E) 1).of_isClosed_subset
            · dsimp [S]
              apply IsClosed.inter (isClosed_eq continuous_norm continuous_const)
              apply IsClosed.inter
              · have heq : (fun u : E => ∀ j ∈ J, a j u ≤ 0) =
                    (⋂ j ∈ J, {u : E | a j u ≤ 0}) := by
                  apply Set.ext; intro u; simp only [Set.mem_iInter, Set.mem_ofPred_eq]; rfl
                rw [heq]
                exact isClosed_biInter fun j hj => isClosed_le (a j).continuous continuous_const
              · have heq : (fun u : E => ∀ v ∈ K J, ‖u‖ ≤ ‖u - v‖) =
                    (⋂ v ∈ K J, {u : E | ‖u‖ ≤ ‖u - v‖}) := by
                  apply Set.ext; intro u; simp only [Set.mem_iInter, Set.mem_ofPred_eq]; rfl
                rw [heq]
                exact isClosed_biInter fun v hv => isClosed_le continuous_norm (continuous_id.sub continuous_const).norm
            · intro u hu
              simpa only [Metric.mem_sphere, dist_zero_right] using hu.1
          have hconst (J : Finset (Fin k)) : ∃ C : ℝ, 0 < C ∧ ∀ u ∈ S J, 1 ≤ C * |g u| := by
            by_cases hneS : (S J).Nonempty
            · obtain ⟨u, hu, hmin⟩ := (hc J).exists_isMinOn hneS (g.continuous.abs.continuousOn)
              have hpos : 0 < |g u| := by
                apply abs_pos.mpr
                intro hz
                have hku : u ∈ K J := ⟨hu.2.1, hz⟩
                have h := hu.2.2 u hku
                simp only [sub_self, norm_zero, hu.1] at h
                norm_num at h
              refine ⟨1 / |g u|, by positivity, ?_⟩
              intro v hv
              have hle := hmin hv
              dsimp [IsMinOn] at hle
              have hh : 1 ≤ |g v| / |g u| := (le_div_iff₀ hpos).2 (by simpa using hle)
              simpa [div_eq_mul_inv, mul_comm] using hh
            · exact ⟨1, by norm_num, fun u hu => False.elim (hneS ⟨u, hu⟩)⟩
          choose C hC hCbound using hconst
          let B : ℝ := ∑ J : Finset (Fin k), C J
          have hB : 0 ≤ B := Finset.sum_nonneg fun J _ => (hC J).le
          refine ⟨B, hB, ?_⟩
          intro x hx
          let Q : Set E := {y | (∀ j, a j y ≤ b j) ∧ g y = c}
          have hQclosed : IsClosed Q := by
            dsimp [Q]
            simp only [Set.ofPred_and, Set.ofPred_forall]
            exact (isClosed_iInter fun j => isClosed_le (a j).continuous continuous_const).inter
              (isClosed_eq g.continuous continuous_const)
          have hQne : Q.Nonempty := hne
          obtain ⟨y, hy, hmin⟩ := hQclosed.exists_infDist_eq_dist hQne x
          refine ⟨y, hy.1, hy.2, ?_⟩
          let u := x - y
          let J : Finset (Fin k) := Finset.univ.filter (fun j => a j y = b j)
          have huJ : ∀ j ∈ J, a j u ≤ 0 := by
            intro j hj
            have hj' := (Finset.mem_filter.mp hj).2
            dsimp [u]
            rw [map_sub, hj']
            linarith [hx j]
          have hminu : ∀ v ∈ K J, ‖u‖ ≤ ‖u - v‖ := by
            intro v hv
            have hv' : ∀ j, a j y = b j → a j v ≤ 0 := by
              intro j hj
              exact hv.1 j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
            obtain ⟨t, ht, ht1, htv⟩ := hlocal k a b y v hy.1 hv'
            have hq : y + t • v ∈ Q := by
              refine ⟨htv, ?_⟩
              simp [hy.2, hv.2]
            have hm : ‖u‖ ≤ ‖u - t • v‖ := by
              have hh := Metric.infDist_le_dist_of_mem (x := x) hq
              rw [hmin, _root_.dist_eq_norm, _root_.dist_eq_norm] at hh
              simpa only [u, sub_add_eq_sub_sub] using hh
            have heq : u - t • v = (1 - t) • u + t • (u - v) := by module
            rw [heq] at hm
            have hn := norm_add_le ((1 - t) • u) (t • (u - v))
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_pos ht] at hn
            nlinarith
          by_cases hu : u = 0
          · have hxy : x - y = 0 := hu
            rw [hxy, norm_zero]
            exact mul_nonneg hB (abs_nonneg _)
          · have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
            let v : E := ‖u‖⁻¹ • u
            have hv : v ∈ S J := by
              refine ⟨?_, ?_, ?_⟩
              · simp [v, norm_smul, abs_of_pos hnu, hnu.ne']
              · intro j hj
                simp only [v, map_smul, smul_eq_mul]
                exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hnu.le) (huJ j hj)
              · intro w hw
                have hkw : ‖u‖ • w ∈ K J := by
                  refine ⟨fun j hj => ?_, ?_⟩
                  · simp only [map_smul, smul_eq_mul]
                    exact mul_nonpos_of_nonneg_of_nonpos hnu.le (hw.1 j hj)
                  · simp [hw.2]
                have hm := hminu (‖u‖ • w) hkw
                have heq : v - w = ‖u‖⁻¹ • (u - ‖u‖ • w) := by
                  simp [v, smul_sub, smul_smul, hnu.ne']
                calc
                  ‖v‖ = ‖u‖⁻¹ * ‖u‖ := by simp [v, norm_smul, abs_of_pos hnu]
                  _ ≤ ‖u‖⁻¹ * ‖u - ‖u‖ • w‖ := mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hnu.le)
                  _ = ‖v - w‖ := by rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnu]
            have hh := hCbound J v hv
            have hCJ : C J ≤ B := Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ J)
            have hg : g v = ‖u‖⁻¹ * (g x - c) := by simp [v, u, hy.2]
            rw [hg, abs_mul, abs_inv, abs_of_pos hnu] at hh
            change ‖u‖ ≤ B * |g x - c|
            have hh' : ‖u‖ ≤ C J * |g x - c| := by
              have hhdiv : 1 ≤ (C J * |g x - c|) / ‖u‖ := by
                simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh
              simpa using (le_div_iff₀ hnu).mp hhdiv
            exact hh'.trans (mul_le_mul_of_nonneg_right hCJ (abs_nonneg _))
        have hfaces (k : ℕ) (a : Fin k → E →L[ℝ] ℝ) (b : Fin k → ℝ) :
            {F : Set E | F.Nonempty ∧ ∃ w : E →L[ℝ] ℝ, ∃ t : ℝ,
              (∀ x, (∀ j, a j x ≤ b j) → w x ≤ t) ∧
              F = {x | (∀ j, a j x ≤ b j) ∧ w x = t}}.Finite := by
          let P : Set E := {x | ∀ j, a j x ≤ b j}
          let R (J : Finset (Fin k)) : Set E := {x | x ∈ P ∧ ∀ j ∈ J, a j x = b j}
          apply (Set.finite_range R).subset
          intro F hF
          obtain ⟨hne, w, t, hw, rfl⟩ := hF
          let F : Set E := {x | (∀ j, a j x ≤ b j) ∧ w x = t}
          have hconv : Convex ℝ F := by
            intro x hx y hy u v hu hv huv
            refine ⟨fun j => ?_, ?_⟩
            · simp only [map_add, map_smul, smul_eq_mul]
              calc
                u * a j x + v * a j y ≤ u * b j + v * b j :=
                  add_le_add (mul_le_mul_of_nonneg_left (hx.1 j) hu)
                    (mul_le_mul_of_nonneg_left (hy.1 j) hv)
                _ = b j := by rw [← add_mul, huv, one_mul]
            · simp only [map_add, map_smul, smul_eq_mul, hx.2, hy.2]
              rw [← add_mul, huv, one_mul]
          have hpoint : ∀ s : Finset (Fin k), ∃ y ∈ F,
              ∀ j ∈ s, (∃ x ∈ F, a j x < b j) → a j y < b j := by
            intro s
            induction s using Finset.induction_on with
            | empty => obtain ⟨y, hy⟩ := hne; exact ⟨y, hy, by simp⟩
            | @insert j s hjs ih =>
              obtain ⟨y, hy, hys⟩ := ih
              by_cases hj : ∃ x ∈ F, a j x < b j
              · obtain ⟨x, hx, hjx⟩ := hj
                let z : E := (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y
                refine ⟨z, hconv hx hy (by norm_num) (by norm_num) (by norm_num), ?_⟩
                intro l hl hl'
                simp only [Finset.mem_insert] at hl
                have hzl : a l z = (1 / 2 : ℝ) * a l x + (1 / 2 : ℝ) * a l y := by simp [z]
                rcases hl with rfl | hl
                · linarith [hy.1 l]
                · have hly := hys l hl hl'
                  linarith [hx.1 l]
              · refine ⟨y, hy, ?_⟩
                intro l hl hl'
                rcases Finset.mem_insert.mp hl with rfl | hl
                · exact False.elim (hj hl')
                · exact hys l hl hl'
          obtain ⟨y, hy, hys⟩ := hpoint Finset.univ
          let J : Finset (Fin k) := Finset.univ.filter (fun j => a j y = b j)
          refine ⟨J, ?_⟩
          symm
          apply Set.ext
          intro x
          constructor
          · intro hx
            refine ⟨hx.1, ?_⟩
            intro j hj
            have hjy := (Finset.mem_filter.mp hj).2
            by_contra hjx
            have hlt : a j x < b j := lt_of_le_of_ne (hx.1 j) hjx
            have := hys j (Finset.mem_univ _) ⟨x, hx, hlt⟩
            linarith
          · intro hx
            refine ⟨hx.1, ?_⟩
            have hv : ∀ j, a j y = b j → a j (y - x) ≤ 0 := by
              intro j hj
              have hjx := hx.2 j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
              simp [map_sub, hj, hjx]
            obtain ⟨s, hs, hs1, hsp⟩ := hlocal k a b y (y - x) hy.1 hv
            have hwz := hw (y + s • (y - x)) hsp
            have hwx := hw x hx.1
            simp only [map_add, map_smul, map_sub, smul_eq_mul, hy.2] at hwz
            nlinarith
        let L (v : Fin d → ℝ) : E →L[ℝ] ℝ :=
          LinearMap.toContinuousLinearMap
            { toFun := fun x => v ⬝ᵥ WithLp.ofLp x
              map_add' := by
                intro x y
                change v ⬝ᵥ (x.ofLp + y.ofLp) = _
                exact dotProduct_add _ _ _
              map_smul' := by
                intro c x
                change v ⬝ᵥ (c • x.ofLp) = c * (v ⬝ᵥ x.ofLp)
                exact dotProduct_smul _ _ _ }
        have hL (v : Fin d → ℝ) (x : E) : L v x = v ⬝ᵥ WithLp.ofLp x := rfl
        obtain ⟨k, A, b, hT⟩ := hTpoly
        let P : Set E := {x | ∀ j, L (A j) x ≤ b j}
        let e := WithLp.linearEquiv p ℝ (Fin d → ℝ)
        have hP (x : E) : x ∈ P ↔ WithLp.ofLp x ∈ T := by rw [hT]; rfl
        have hfinite : {F : Set (Fin d → ℝ) | IsFaceOf T F}.Finite := by
          apply ((hfaces k (fun j => L (A j)) b).image (fun F : Set E => e '' F)).subset
          intro F hF
          let F' : Set E := WithLp.ofLp ⁻¹' F
          have hne' : F'.Nonempty := by
            obtain ⟨x, hx⟩ := hF.1
            exact ⟨WithLp.toLp p x, hx⟩
          have heq : e '' F' = F := by
            ext x
            constructor
            · rintro ⟨y, hy, rfl⟩; exact hy
            · intro hx; exact ⟨WithLp.toLp p x, hx, rfl⟩
          refine ⟨F', ?_, heq⟩
          refine ⟨hne', ?_⟩
          rcases hF.2 with hzero | hfull | ⟨w, t, hw, hFw⟩
          · exact False.elim (hF.1.ne_empty hzero)
          · refine ⟨0, 0, by simp, ?_⟩
            ext x
            simp only [F', Set.mem_preimage, hfull, ← hP, P, Set.mem_ofPred_eq,
              _root_.zero_apply, and_true]
          · refine ⟨L w, t, ?_, ?_⟩
            · intro x hx
              exact hw.2.1 ((hP x).mp hx)
            · ext x
              simp only [F', Set.mem_preimage, hFw, Set.mem_inter_iff, Set.mem_ofPred_eq]
              rw [← hP x]
              rfl
        have hrep (F : Set (Fin d → ℝ)) (hF : IsFaceOf T F) :
            ∃ l : ℕ, ∃ a : Fin l → E →L[ℝ] ℝ, ∃ b' : Fin l → ℝ,
              ∀ x : E, WithLp.ofLp x ∈ F ↔ ∀ j, a j x ≤ b' j := by
          rcases hF.2 with hz | hf | ⟨w, t, hw, hf⟩
          · exact False.elim (hF.1.ne_empty hz)
          · refine ⟨k, fun j => L (A j), b, ?_⟩
            intro x
            rw [hf, hT]
            rfl
          · refine ⟨k + 1 + 1, Fin.snoc (Fin.snoc (fun j => L (A j)) (L w)) (-L w),
              Fin.snoc (Fin.snoc b t) (-t), ?_⟩
            intro x
            rw [hf, hT]
            simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Fin.forall_fin_succ',
              Fin.snoc_castSucc, Fin.snoc_last, _root_.neg_apply]
            change ((∀ j, L (A j) x ≤ b j) ∧ L w x = t) ↔
              ((∀ j, L (A j) x ≤ b j) ∧ L w x ≤ t) ∧ -L w x ≤ -t
            constructor
            · rintro ⟨hx, hwx⟩; exact ⟨⟨hx, hwx.le⟩, by linarith⟩
            · rintro ⟨⟨hx, hle⟩, hge⟩; exact ⟨hx, by linarith⟩
        have htheta (F : Set (Fin d → ℝ)) (hF : IsFaceOf T F) (i : Fin mt)
            (hFi : (F ∩ hyperplane M i).Nonempty) : thetaFace M p F i < ⊤ := by
          obtain ⟨l, a, b', hrepF⟩ := hrep F hF
          let g := L (M.G i)
          let c := M.g0 i
          have hH (x : E) : WithLp.ofLp x ∈ hyperplane M i ↔ g x = c := Iff.rfl
          have hne : ∃ y : E, (∀ j, a j y ≤ b' j) ∧ g y = c := by
            obtain ⟨z, hzF, hzH⟩ := hFi
            exact ⟨WithLp.toLp p z, (hrepF _).mp hzF, hzH⟩
          obtain ⟨C, hC, hCb⟩ := hbound l a b' g c hne
          let D : ℝ := C * ‖g‖
          have hD : 0 ≤ D := mul_nonneg hC (norm_nonneg _)
          have hworks : ∀ ζ ∈ F, ptDist p ζ (F ∩ hyperplane M i) ≤
              (D : EReal) * ptDist p ζ (hyperplane M i) := by
            intro ζ hζ
            let x : E := WithLp.toLp p ζ
            obtain ⟨y, hyF, hyH, hxy⟩ := hCb x ((hrepF x).mp hζ)
            let H : Set E := {z | g z = c}
            have hHcl : IsClosed H := isClosed_eq g.continuous continuous_const
            have hHne : H.Nonempty := by obtain ⟨z, hz, hz'⟩ := hne; exact ⟨z, hz'⟩
            obtain ⟨z, hz, hmin⟩ := hHcl.exists_infDist_eq_dist hHne x
            have hdist : ptDist p ζ (hyperplane M i) = (‖x - z‖ : EReal) := by
              apply le_antisymm
              · exact iInf_le_of_le z.ofLp (iInf_le_of_le ((hH z).mpr hz) (by simp [x, WithLp.toLp_sub]))
              · apply le_iInf
                intro z'
                apply le_iInf
                intro hz'
                apply EReal.coe_le_coe
                have hh := Metric.infDist_le_dist_of_mem (x := x) (s := H) ((hH (WithLp.toLp p z')).mp hz')
                rw [hmin, dist_eq_norm, dist_eq_norm] at hh
                simpa [x, WithLp.toLp_sub] using hh
            have hgap : |g x - c| ≤ ‖g‖ * ‖x - z‖ := by
              have hh := g.le_opNorm (x - z)
              have hgz : g z = c := hz
              simpa only [map_sub, hgz, Real.norm_eq_abs] using hh
            have hreal : ‖x - y‖ ≤ D * ‖x - z‖ := by
              calc
                ‖x - y‖ ≤ C * |g x - c| := hxy
                _ ≤ C * (‖g‖ * ‖x - z‖) := mul_le_mul_of_nonneg_left hgap hC
                _ = D * ‖x - z‖ := by dsimp [D]; ring
            rw [hdist, ← EReal.coe_mul]
            have hub : ptDist p ζ (F ∩ hyperplane M i) ≤
                ((‖WithLp.toLp p (ζ - y.ofLp)‖ : ℝ) : EReal) := by
              unfold ptDist
              exact iInf_le_of_le y.ofLp (iInf_le_of_le
                ⟨(hrepF y).mpr hyF, (hH y).mpr hyH⟩ le_rfl)
            apply hub.trans
            apply EReal.coe_le_coe
            simpa [x, WithLp.toLp_sub] using hreal
          exact lt_of_le_of_lt (sInf_le ⟨D, hD, rfl, hworks⟩) (EReal.coe_lt_top D)
        have hsup {α : Type} (s : Set α) (hs : s.Finite) (f : α → EReal)
            (hf : ∀ x ∈ s, f x < ⊤) : (⨆ x ∈ s, f x) < ⊤ := by
          revert hf
          induction s, hs using Set.Finite.induction_on with
          | empty => simp
          | @insert x s hx hs ih =>
            intro hf
            rw [iSup_insert]
            exact max_lt (hf x (Set.mem_insert _ _)) (ih (fun y hy => hf y (Set.mem_insert_of_mem _ hy)))
        constructor
        · exact le_max_left _ _
        · change max 1 _ < ⊤
          apply max_lt (EReal.coe_lt_top 1)
          apply hsup _ hfinite
          intro F hF
          apply hsup _ (Set.toFinite _)
          intro i hi
          exact htheta F hF i hi
