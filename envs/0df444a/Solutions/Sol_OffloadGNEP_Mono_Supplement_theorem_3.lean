-- Prove2me | solution 1 for OffloadGNEP.Mono.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:19:40.638796+00:00
-- url     : https://prove2.me/submissions/5c472dc6-92b2-446f-94fe-1e2b6ebe50ba

import Mathlib
import Definitions.Def_OffloadGNEP_Mono_Supplement_Algorithms

open OffloadGNEP
open OffloadGNEP.Mono
open OffloadGNEP.Mono.Supplement

open OffloadGNEP.Ext Filter Topology

theorem solution {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (hD : ∀ x ∈ Kprod P, load P x < 1) (hM : IsMonotoneOnE (Ke P) (Fe P)) :
    (∀ α : ℝ, alphaBar P < α →
      (∀ c ∈ Ke P, ∃! p, IsVISolE (Ke P) (regMap P α c) p) ∧
      (∀ c ∈ Ke P, ∀ z ∈ Ke P, ∃! z', IsAlg2Step P α c z z') ∧
      (∀ t, IsAlg1Run P α t →
        ∃ z, IsVISolE (Ke P) (Fe P) z ∧ Tendsto t atTop (𝓝 z))) ∧
    ∃ αbar : ℝ, 0 < αbar ∧ ∀ α : ℝ, αbar < α →
      ∀ c ∈ Ke P, ∀ s, IsAlg2Run P α c s →
        ∀ p, IsVISolE (Ke P) (regMap P α c) p → Tendsto s atTop (𝓝 p) := by
          have lemA : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
                 (C : Set H) (hne : C.Nonempty) (hcl : IsClosed C) (hcv : Convex ℝ C) (G : H → H) (μ L : ℝ)
                 (hμ : 0 < μ) (hL : ∀ x ∈ C, ∀ y ∈ C, ‖G x - G y‖ ≤ L * ‖x - y‖)
                 (hm : ∀ x ∈ C, ∀ y ∈ C, μ * ‖x - y‖ ^ 2 ≤ inner ℝ (G x - G y) (x - y)),
              ∃! x, x ∈ C ∧ ∀ y ∈ C, 0 ≤ inner ℝ (G x) (y - x) := by
            clear hA hS hD hM P
            intro H _ _ _ C hne hcl hcv G μ L hμ hL hm
            have hproj : ∀ x : H, ∃ v ∈ C, ∀ w ∈ C, inner ℝ (x - v) (w - v) ≤ 0 := by
              intro x
              obtain ⟨v, hv, h⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hcv x
              exact ⟨v, hv, (norm_eq_iInf_iff_real_inner_le_zero hcv hv).1 h⟩
            choose pr hprC hpr using hproj
            have hnon : ∀ x y, ‖pr x - pr y‖ ≤ ‖x - y‖ := by
              intro x y
              have h1 := hpr x (pr y) (hprC y)
              have h2 := hpr y (pr x) (hprC x)
              have h3 : ‖pr x - pr y‖ ^ 2 ≤ inner ℝ (x - y) (pr x - pr y) := by
                rw [← real_inner_self_eq_norm_sq]
                have e : inner ℝ (x - y) (pr x - pr y) - inner ℝ (pr x - pr y) (pr x - pr y) =
                  - inner ℝ (x - pr x) (pr y - pr x) - inner ℝ (y - pr y) (pr x - pr y) := by
                  simp only [inner_sub_left, inner_sub_right]; ring
                linarith
              have h4 := real_inner_le_norm (x - y) (pr x - pr y)
              by_contra hc
              push Not at hc
              have h5 := mul_lt_mul_of_pos_right hc ((norm_nonneg (x - y)).trans_lt hc)
              rw [sq] at h3
              linarith
            obtain ⟨L', hL'0, hL'μ, hL'⟩ : ∃ L' : ℝ, 0 < L' ∧ μ ≤ L' ∧ ∀ x ∈ C, ∀ y ∈ C, ‖G x - G y‖ ≤ L' * ‖x - y‖ := by
              refine ⟨max L μ, lt_max_of_lt_right hμ, le_max_right _ _, fun x hx y hy => ?_⟩
              exact (hL x hx y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
            set τ : ℝ := μ / L' ^ 2 with hτ
            have hτ0 : 0 < τ := by positivity
            set k : ℝ := Real.sqrt (1 - μ ^ 2 / L' ^ 2) with hk
            have hfrac : μ ^ 2 / L' ^ 2 ≤ 1 := by
              rw [div_le_one (by positivity)]; exact pow_le_pow_left₀ hμ.le hL'μ 2
            have hfrac0 : 0 < μ ^ 2 / L' ^ 2 := by positivity
            have hk0 : 0 ≤ k := Real.sqrt_nonneg _
            have hk1 : k < 1 := by
              rw [hk, Real.sqrt_lt' one_pos]; linarith
            have hksq : k ^ 2 = 1 - μ ^ 2 / L' ^ 2 := Real.sq_sqrt (by linarith)
            have hstep : ∀ x ∈ C, ∀ y ∈ C, ‖(x - τ • G x) - (y - τ • G y)‖ ≤ k * ‖x - y‖ := by
              intro x hx y hy
              have e1 : (x - τ • G x) - (y - τ • G y) = (x - y) - τ • (G x - G y) := by
                rw [smul_sub]; abel
              have e2 : ‖(x - y) - τ • (G x - G y)‖ ^ 2 ≤ (k * ‖x - y‖) ^ 2 := by
                rw [norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, mul_pow, hksq, Real.norm_eq_abs, sq_abs,
                  real_inner_comm]
                have h1 := hm x hx y hy
                have h2 : ‖G x - G y‖ ^ 2 ≤ L' ^ 2 * ‖x - y‖ ^ 2 := by
                  rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hL' x hx y hy) 2
                have h3 : τ * (μ * ‖x - y‖ ^ 2) ≤ τ * inner ℝ (G x - G y) (x - y) :=
                  mul_le_mul_of_nonneg_left h1 hτ0.le
                have h4 : τ ^ 2 * ‖G x - G y‖ ^ 2 ≤ τ ^ 2 * (L' ^ 2 * ‖x - y‖ ^ 2) :=
                  mul_le_mul_of_nonneg_left h2 (by positivity)
                have h5 : τ ^ 2 * (L' ^ 2 * ‖x - y‖ ^ 2) = μ ^ 2 / L' ^ 2 * ‖x - y‖ ^ 2 := by
                  rw [hτ]; field_simp
                have h6 : τ * (μ * ‖x - y‖ ^ 2) = μ ^ 2 / L' ^ 2 * ‖x - y‖ ^ 2 := by
                  rw [hτ]; field_simp
                linear_combination 2 * h3 + h4 + h5 - 2 * h6
              rw [e1]
              exact le_of_sq_le_sq e2 (by positivity)
            let T : H → H := fun x => pr (pr x - τ • G (pr x))
            have hT : ContractingWith ⟨k, hk0⟩ T := by
              refine ⟨by exact_mod_cast hk1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
              rw [dist_eq_norm, dist_eq_norm]
              calc ‖T x - T y‖ ≤ ‖(pr x - τ • G (pr x)) - (pr y - τ • G (pr y))‖ := hnon _ _
                _ ≤ k * ‖pr x - pr y‖ := hstep _ (hprC x) _ (hprC y)
                _ ≤ k * ‖x - y‖ := mul_le_mul_of_nonneg_left (hnon x y) hk0
            have hne' : Nonempty H := ⟨hne.some⟩
            set x := ContractingWith.fixedPoint T hT with hx
            have hfix : T x = x := hT.fixedPoint_isFixedPt
            have hxC : x ∈ C := by rw [← hfix]; exact hprC _
            have hprx : pr x = x := by
              have h1 := hpr x x hxC
              rw [real_inner_self_eq_norm_sq] at h1
              have : ‖x - pr x‖ = 0 := (pow_eq_zero_iff two_ne_zero).1 (le_antisymm h1 (sq_nonneg _))
              exact (sub_eq_zero.1 (norm_eq_zero.1 this)).symm
            refine ⟨x, ⟨hxC, fun y hy => ?_⟩, ?_⟩
            · have h1 := hpr (pr x - τ • G (pr x)) y hy
              have h2 : pr (pr x - τ • G (pr x)) = x := hfix
              rw [h2, hprx] at h1
              have e : x - τ • G x - x = - (τ • G x) := by abel
              rw [e, inner_neg_left, real_inner_smul_left] at h1
              by_contra hc
              push Not at hc
              have := mul_neg_of_pos_of_neg hτ0 hc
              linarith
            · rintro y ⟨hyC, hy⟩
              have h1 := hm x hxC y hyC
              have h2 := hy x hxC
              have h3 : 0 ≤ inner ℝ (G x) (y - x) := by
                have h1 := hpr (pr x - τ • G (pr x)) y hyC
                have h2 : pr (pr x - τ • G (pr x)) = x := hfix
                rw [h2, hprx] at h1
                have e : x - τ • G x - x = - (τ • G x) := by abel
                rw [e, inner_neg_left, real_inner_smul_left] at h1
                by_contra hc
                push Not at hc
                have := mul_neg_of_pos_of_neg hτ0 hc
                linarith
              have e : inner ℝ (G x - G y) (x - y) = - inner ℝ (G x) (y - x) - inner ℝ (G y) (x - y) := by
                simp only [inner_sub_left, inner_sub_right]; ring
              have h4 : ‖x - y‖ = 0 := by
                have : ‖x - y‖ ^ 2 ≤ 0 := by
                  by_contra hc
                  push Not at hc
                  have := mul_pos hμ hc
                  linarith
                exact (pow_eq_zero_iff two_ne_zero).1 (le_antisymm this (sq_nonneg _))
              exact (sub_eq_zero.1 (norm_eq_zero.1 h4)).symm
          have lemB : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [ProperSpace H]
                 (C : Set H) (hcl : IsClosed C) (G : H → H) (hG : ContinuousOn G C)
                 (hm : ∀ x ∈ C, ∀ y ∈ C, 0 ≤ inner ℝ (G x - G y) (x - y))
                 (z : H) (hzC : z ∈ C) (hz : ∀ y ∈ C, 0 ≤ inner ℝ (G z) (y - z))
                 (α : ℝ) (hα : 0 < α) (t : ℕ → H)
                 (ht : ∀ k, t (k+1) ∈ C ∧ ∀ y ∈ C, 0 ≤ inner ℝ (G (t (k+1)) + α • (t (k+1) - t k)) (y - t (k+1))),
              ∃ x ∈ C, (∀ y ∈ C, 0 ≤ inner ℝ (G x) (y - x)) ∧ Tendsto t atTop (𝓝 x) := by
            clear hA hS hD hM lemA P
            intro H _ _ _ C hcl G hG hm z hzC hz α hα t ht
            have hF : ∀ z ∈ C, (∀ y ∈ C, 0 ≤ inner ℝ (G z) (y - z)) → ∀ k,
                ‖t (k+1) - z‖ ^ 2 + ‖t (k+1) - t k‖ ^ 2 ≤ ‖t k - z‖ ^ 2 := by
              intro z hzC hz k
              obtain ⟨h1, h2⟩ := ht k
              have h3 := h2 z hzC
              have h4 := hz _ h1
              have h5 := hm _ h1 _ hzC
              have h6 : 0 ≤ inner ℝ (t (k+1) - t k) (z - t (k+1)) := by
                rw [inner_add_left, real_inner_smul_left] at h3
                have e : inner ℝ (G (t (k+1)) - G z) (t (k+1) - z) =
                  - inner ℝ (G (t (k+1))) (z - t (k+1)) - inner ℝ (G z) (t (k+1) - z) := by
                  simp only [inner_sub_left, inner_sub_right]; ring
                have : 0 ≤ α * inner ℝ (t (k+1) - t k) (z - t (k+1)) := by linarith
                by_contra hc
                push Not at hc
                have := mul_neg_of_pos_of_neg hα hc
                linarith
              have e : ‖t k - z‖ ^ 2 = ‖t (k+1) - z‖ ^ 2 + ‖t (k+1) - t k‖ ^ 2 +
                  2 * inner ℝ (t (k+1) - t k) (z - t (k+1)) := by
                simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right]
                rw [real_inner_comm z (t k), real_inner_comm z (t (k+1)), real_inner_comm (t k) (t (k+1))]
                ring
              linarith
            have hanti : ∀ z ∈ C, (∀ y ∈ C, 0 ≤ inner ℝ (G z) (y - z)) →
                Antitone fun k => ‖t k - z‖ ^ 2 := by
              intro z hzC hz
              refine antitone_nat_of_succ_le fun k => ?_
              have := hF z hzC hz k
              linarith [sq_nonneg ‖t (k+1) - t k‖]
            have hconv : ∃ l, Tendsto (fun k => ‖t k - z‖ ^ 2) atTop (𝓝 l) :=
              ⟨_, tendsto_atTop_ciInf (hanti z hzC hz) ⟨0, by rintro _ ⟨k, rfl⟩; positivity⟩⟩
            obtain ⟨l, hl⟩ := hconv
            have hd2 : Tendsto (fun k => ‖t (k+1) - t k‖ ^ 2) atTop (𝓝 0) := by
              have h1 : Tendsto (fun k => ‖t k - z‖ ^ 2 - ‖t (k+1) - z‖ ^ 2) atTop (𝓝 (l - l)) :=
                hl.sub (hl.comp (tendsto_add_atTop_nat 1))
              rw [sub_self] at h1
              refine squeeze_zero (fun k => by positivity) (fun k => ?_) h1
              have := hF z hzC hz k
              linarith
            have hd : Tendsto (fun k => t (k+1) - t k) atTop (𝓝 0) := by
              rw [tendsto_zero_iff_norm_tendsto_zero]
              have := hd2.sqrt
              simpa [Real.sqrt_sq] using this
            have hbd : ∀ k, t k ∈ Metric.closedBall z ‖t 0 - z‖ := by
              intro k
              have h := hanti z hzC hz (Nat.zero_le k)
              rw [mem_closedBall_iff_norm]
              exact le_of_sq_le_sq h (norm_nonneg _)
            obtain ⟨x, -, φ, hφ, hx⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbd
            have hx' : Tendsto (fun k => t (φ k + 1)) atTop (𝓝 x) := by
              have h1 := (hd.comp hφ.tendsto_atTop).add hx
              simpa using h1
            have hxC : x ∈ C := hcl.mem_of_tendsto hx' (Eventually.of_forall fun k => (ht _).1)
            have hGx : Tendsto (fun k => G (t (φ k + 1))) atTop (𝓝 (G x)) :=
              (hG x hxC).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hx', Eventually.of_forall fun k => (ht _).1⟩)
            have hxsol : ∀ y ∈ C, 0 ≤ inner ℝ (G x) (y - x) := by
              intro y hy
              have h1 : Tendsto (fun k => inner ℝ (G (t (φ k + 1)) + α • (t (φ k + 1) - t (φ k))) (y - t (φ k + 1)))
                  atTop (𝓝 (inner ℝ (G x + α • (0:H)) (y - x))) :=
                (hGx.add ((hd.comp hφ.tendsto_atTop).const_smul α)).inner (tendsto_const_nhds.sub hx')
              rw [smul_zero, add_zero] at h1
              exact ge_of_tendsto' h1 fun k => (ht (φ k)).2 y hy
            refine ⟨x, hxC, hxsol, ?_⟩
            have hA := hanti x hxC hxsol
            have h1 : Tendsto (fun k => ‖t (φ k) - x‖ ^ 2) atTop (𝓝 0) := by
              have := (hx.sub_const x).norm.pow 2
              simpa using this
            have h2 : Tendsto (fun k => ‖t k - x‖ ^ 2) atTop (𝓝 0) := by
              rw [Metric.tendsto_atTop]
              intro ε hε
              obtain ⟨n, hn⟩ := Metric.tendsto_atTop.1 h1 ε hε
              refine ⟨φ n, fun k hk => ?_⟩
              have h3 := hn n le_rfl
              have h4 := hA hk
              rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h3 ⊢
              exact lt_of_le_of_lt h4 h3
            rw [tendsto_iff_norm_sub_tendsto_zero]
            have := h2.sqrt
            simpa [Real.sqrt_sq] using this
          have sumT : ∀ (f : Exist.Tier → ℝ),
              ∑ i, f i = f .m + f .clet + f .cloud := by
            clear hA hS hD hM lemA lemB P
            intro f
            have : (Finset.univ : Finset Exist.Tier) = {Exist.Tier.m, Exist.Tier.clet, Exist.Tier.cloud} := rfl
            rw [this, Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]; ring
          have ktilClosed : ∀ {N : ℕ} (P : Params N) (u : Fin N),
              IsCompact (Ktil P u) := by
            clear hA hS hD hM lemA lemB sumT P
            intro N P u
            have hcl : IsClosed (Ktil P u) := by
              unfold Ktil
              refine IsClosed.and ?_ (IsClosed.and ?_ (IsClosed.and ?_ ?_))
              · simp only [Set.ofPred_forall]
                exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
              · exact isClosed_eq (by fun_prop) (by fun_prop)
              · exact isClosed_le (by fun_prop) (by fun_prop)
              · exact isClosed_le (by fun_prop) (by fun_prop)
            refine IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : Exist.Tier → ℝ)) (b := fun _ => 1)) hcl ?_
            rintro y ⟨h0, h1, -, -⟩
            refine ⟨fun i => h0 i, fun i => ?_⟩
            have a := h0 .m
            have b := h0 .clet
            have c := h0 .cloud
            cases i <;> simp <;> linarith
          have ktilConvex : ∀ {N : ℕ} (P : Params N) (u : Fin N),
              Convex ℝ (Ktil P u) := by
            clear hA hS hD hM lemA lemB sumT ktilClosed P
            intro N P u
            rintro x ⟨hx0, hx1, hx2, hx3⟩ y ⟨hy0, hy1, hy2, hy3⟩ a b ha hb hab
            refine ⟨fun i => ?_, ?_, ?_, ?_⟩
            · have := mul_nonneg ha (hx0 i)
              have := mul_nonneg hb (hy0 i)
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linarith
            · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              linear_combination a * hx1 + b * hy1 + hab
            · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              have e : P.chi = a * P.chi + b * P.chi := by rw [← add_mul, hab, one_mul]
              linarith [mul_le_mul_of_nonneg_left hx2 ha, mul_le_mul_of_nonneg_left hy2 hb]
            · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              have e : P.Pmax u = a * P.Pmax u + b * P.Pmax u := by rw [← add_mul, hab, one_mul]
              linarith [mul_le_mul_of_nonneg_left hx3 ha, mul_le_mul_of_nonneg_left hy3 hb]
          have kprodCompact : ∀ {N : ℕ} (P : Params N),
              IsCompact (Kprod P) := by
            clear hA hS hD hM lemA lemB sumT ktilConvex P
            intro N P
            have : Kprod P = Set.pi Set.univ (Ktil P) := by ext x; simp [Kprod]
            rw [this]; exact isCompact_univ_pi (ktilClosed P)
          have kprodConvex : ∀ {N : ℕ} (P : Params N),
              Convex ℝ (Kprod P) := by
            clear hA hS hD hM lemA lemB sumT ktilClosed kprodCompact P
            intro N P
            intro x hx y hy a b ha hb hab u
            exact ktilConvex P u (hx u) (hy u) ha hb hab
          have keClosed : ∀ {N : ℕ} (P : Params N),
              IsClosed (Ke P) := by
            clear hA hS hD hM lemA lemB sumT ktilClosed ktilConvex kprodConvex P
            intro N P
            have : Ke P = Kprod P ×ˢ Set.Ici 0 := by ext x; simp [Ke]
            rw [this]; exact (kprodCompact P).isClosed.prod isClosed_Ici
          have keConvex : ∀ {N : ℕ} (P : Params N),
              Convex ℝ (Ke P) := by
            clear hA hS hD hM lemA lemB sumT ktilClosed ktilConvex kprodCompact keClosed P
            intro N P
            have : Ke P = Kprod P ×ˢ Set.Ici 0 := by ext x; simp [Ke]
            rw [this]; exact (kprodConvex P).prod (convex_Ici 0)
          have le1 : ∀ {N : ℕ} (P : Params N) (hA : P.AssumptionA) (x) (hx : x ∈ Kprod P) (u : Fin N),
              0 < 1 - P.alpha u * x u .m := by
            clear hA hS hD hM lemA lemB sumT ktilClosed ktilConvex kprodCompact kprodConvex keClosed keConvex P
            intro N P hA x hx u
            obtain ⟨h0, h1, -, -⟩ := hx u
            obtain ⟨a0, a1, -, -⟩ := hA.2.2 u
            have a := h0 .m
            have b := h0 .clet
            have c := h0 .cloud
            nlinarith
          have lipF : ∀ {N : ℕ} (P : Params N) (hA : P.AssumptionA) 
                 (hD : ∀ x ∈ Kprod P, load P x < 1),
              ∃ L : ℝ, 0 ≤ L ∧ (∀ x ∈ Kprod P, ∀ y ∈ Kprod P, ‖F P x - F P y‖ ≤ L * ‖x - y‖) ∧ ∀ x ∈ Kprod P, ∀ y ∈ Kprod P, |load P x - load P y| ≤ L * ‖x - y‖ := by
            clear hA hS hD hM lemA lemB sumT ktilClosed ktilConvex keClosed keConvex P
            intro N P hA hD
            have hl : ContDiff ℝ 1 (load P) := by unfold load; fun_prop
            have hF : ContDiffOn ℝ 1 (F P) (Kprod P) := by
              rw [contDiffOn_pi]
              intro u
              rw [contDiffOn_pi]
              intro i
              cases i
              · refine ContDiffOn.div (by fun_prop) (by fun_prop) ?_
                intro x hx
                exact pow_ne_zero _ (le1 P hA x hx u).ne'
              · refine ContDiffOn.add (by fun_prop) (ContDiffOn.div (by fun_prop) ?_ ?_)
                · unfold D; exact ((contDiff_const.sub hl).pow 2).contDiffOn
                · intro x hx
                  have := hD x hx
                  exact pow_ne_zero _ (by unfold D; linarith)
              · exact contDiffOn_const
            obtain ⟨K1, h1⟩ := hF.exists_lipschitzOnWith (by simp) (kprodConvex P) (kprodCompact P)
            obtain ⟨K2, h2⟩ := (hl.contDiffOn (s := Kprod P)).exists_lipschitzOnWith (by simp) (kprodConvex P) (kprodCompact P)
            refine ⟨K1 + K2, by positivity, fun x hx y hy => ?_, fun x hx y hy => ?_⟩
            · have := h1.dist_le_mul x hx y hy
              rw [dist_eq_norm, dist_eq_norm] at this
              have : 0 ≤ (K2 : ℝ) * ‖x - y‖ := by positivity
              linarith
            · have := h2.dist_le_mul x hx y hy
              rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs] at this
              have : 0 ≤ (K1 : ℝ) * ‖x - y‖ := by positivity
              linarith
          have lipFe : ∀ {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
                 (hD : ∀ x ∈ Kprod P, load P x < 1),
              ∃ L : ℝ, 0 ≤ L ∧ (∀ p ∈ Ke P, ∀ q ∈ Ke P, ‖Fe P p - Fe P q‖ ≤ L * ‖p - q‖) ∧ ∀ x ∈ Kprod P, ∀ y ∈ Kprod P, |load P x - load P y| ≤ L * ‖x - y‖ := by
            clear hA hS hD hM lemA lemB sumT ktilClosed ktilConvex kprodCompact kprodConvex keClosed keConvex le1 P
            intro N P hA hS hD
            obtain ⟨L, hL0, hL1, hL2⟩ := lipF P hA hD
            refine ⟨L + 1, by positivity, fun p hp q hq => ?_, fun x hx y hy => ?_⟩
            · have n1 : ‖p.1 - q.1‖ ≤ ‖p - q‖ := norm_fst_le (p - q)
              have n2 : ‖p.2 - q.2‖ ≤ ‖p - q‖ := norm_snd_le (p - q)
              have hpr : ‖price P p.2 - price P q.2‖ ≤ ‖p.2 - q.2‖ := by
                rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
                intro u
                rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
                intro i
                simp only [Pi.sub_apply, price]
                split_ifs
                · rw [← sub_mul, norm_mul]
                  obtain ⟨-, -, d0, d1⟩ := hA.2.2 u
                  have hn : (1:ℝ) ≤ P.n := by exact_mod_cast hS.1
                  have : ‖P.delta u / (P.n : ℝ)‖ ≤ 1 := by
                    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one (by linarith)]; linarith
                  exact mul_le_of_le_one_right (norm_nonneg _) this
                · simp
              have k1 := hL1 _ hp.1 _ hq.1
              have k2 := hL2 _ hp.1 _ hq.1
              rw [Prod.norm_def, max_le_iff]
              constructor
              · have e : (Fe P p - Fe P q).1 = (F P p.1 - F P q.1) + (price P p.2 - price P q.2) := by
                  simp only [Fe, Prod.fst_sub]; abel
                rw [e]
                calc _ ≤ ‖F P p.1 - F P q.1‖ + ‖price P p.2 - price P q.2‖ := norm_add_le _ _
                  _ ≤ L * ‖p - q‖ + ‖p - q‖ := add_le_add (k1.trans (by gcongr)) (hpr.trans n2)
                  _ = _ := by ring
              · have e : (Fe P p - Fe P q).2 = -(load P p.1 - load P q.1) := by
                  simp only [Fe, Prod.snd_sub]; ring
                rw [e, norm_neg, Real.norm_eq_abs]
                calc _ ≤ L * ‖p.1 - q.1‖ := k2
                  _ ≤ L * ‖p - q‖ := by gcongr
                  _ ≤ _ := by nlinarith [norm_nonneg (p - q)]
            · have := hL2 x hx y hy
              nlinarith [norm_nonneg (x - y)]
          have updK : ∀ {N : ℕ} (P : Params N) (x) (hx : x ∈ Kprod P) (u : Fin N) (y) (hy : y ∈ Ktil P u),
              Function.update x u y ∈ Kprod P := by
            clear hA hS hD hM lemA lemB sumT ktilClosed ktilConvex kprodCompact kprodConvex keClosed keConvex le1 lipF lipFe P
            intro N P x hx u y hy
            intro v
            by_cases h : v = u
            · subst h; simpa using hy
            · simpa [Function.update_of_ne h] using hx v
          have loadU : ∀ {N : ℕ} (P : Params N) (x : Fin N → Exist.Tier → ℝ) (u : Fin N) (y : Exist.Tier → ℝ),
              load P (Function.update x u y) = (1 / (P.n : ℝ)) * (P.delta u * y .clet + ∑ v ∈ Finset.univ.erase u, P.delta v * x v .clet) := by
            clear hA hS hD hM lemA lemB sumT ktilClosed ktilConvex kprodCompact kprodConvex keClosed keConvex le1 lipF lipFe updK P
            intro N P x u y
            unfold load
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u)]
            congr 2
            · simp
            · refine Finset.sum_congr rfl fun v hv => ?_
              rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
          have objF : ∀ {N : ℕ} (P : Params N) (α : ℝ) (c z : (Fin N → Exist.Tier → ℝ) × ℝ) (u : Fin N)
                  (y : Exist.Tier → ℝ),
              alg2Obj P α c z u y = P.alpha u * y .m / (1 - P.alpha u * y .m) +
                  P.beta u * y .clet + P.gamma u * y .cloud +
                  P.delta u * y .clet / (1 - (1 / (P.n : ℝ)) * (P.delta u * y .clet + ∑ v ∈ Finset.univ.erase u, P.delta v * z.1 v .clet))
                   + z.2 * (P.delta u / (P.n : ℝ) * y .clet) + α / 2 * ((y .m - c.1 u .m) ^ 2 + (y .clet - c.1 u .clet) ^ 2 + (y .cloud - c.1 u .cloud) ^ 2) := by
            clear hA hS hD hM lemA lemB ktilClosed ktilConvex kprodCompact kprodConvex keClosed keConvex le1 lipF lipFe updK P
            intro N P α c z u y
            simp only [alg2Obj, cost, D, loadU, sumT, Function.update_self]
          have foc : ∀ {N : ℕ} (P : Params N) (hA : P.AssumptionA) 
                 (hD : ∀ x ∈ Kprod P, load P x < 1) (α : ℝ) (c z : (Fin N → Exist.Tier → ℝ) × ℝ) (hz : z.1 ∈ Kprod P) (u : Fin N)
                 (w : Exist.Tier → ℝ) (hw : w ∈ Ktil P u) (hmin : ∀ y ∈ Ktil P u, alg2Obj P α c z u w ≤ alg2Obj P α c z u y),
              ∀ y ∈ Ktil P u, 0 ≤ ∑ i, ((Fe P (Function.update z.1 u w, z.2)).1 u i + α * (w i - c.1 u i)) * (y i - w i) := by
            clear hA hS hD hM lemA lemB ktilClosed kprodCompact kprodConvex keClosed keConvex lipF lipFe P
            intro N P hA hD α c z hz u w hw hmin
            intro y hy
            have hU := updK P z.1 hz u w hw
            have hden1 := le1 P hA _ hU u
            have hden2 : 0 < 1 - load P (Function.update z.1 u w) := by linarith [hD _ hU]
            have hFe : ∀ i, (Fe P (Function.update z.1 u w, z.2)).1 u i = F P (Function.update z.1 u w) u i + price P z.2 u i := fun i => rfl
            simp only [hFe, sumT, price, F, D, Function.update_self]
            have herase : ∑ v ∈ Finset.univ.erase u, P.delta v * (Function.update z.1 u w) v .clet = ∑ v ∈ Finset.univ.erase u, P.delta v * z.1 v .clet := 
              Finset.sum_congr rfl fun v hv => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hv)]
            rw [herase]
            rw [loadU] at hden2 ⊢
            rw [Function.update_self] at hden1
            simp only [objF] at hmin
            set S := ∑ v ∈ Finset.univ.erase u, P.delta v * z.1 v .clet with hSdef
            set g : ℝ → ℝ := fun t => alg2Obj P α c z u (w + t • (y - w)) with hg
            have hder : HasDerivAt g ((P.alpha u / (1 - P.alpha u * w .m) ^ 2 + 0 + α * (w .m - c.1 u .m)) * (y .m - w .m) + 
               (P.beta u + P.delta u * (1 - 1 / (P.n:ℝ) * S) / (1 - 1 / (P.n:ℝ) * (P.delta u * w .clet + S)) ^ 2 + z.2 * (P.delta u / (P.n:ℝ)) + α * (w .clet - c.1 u .clet)) * (y .clet - w .clet) + 
               (P.gamma u + 0 + α * (w .cloud - c.1 u .cloud)) * (y .cloud - w .cloud)) 0 := by
              have hl : ∀ i, HasDerivAt (fun t : ℝ => w i + t * (y i - w i)) (y i - w i) 0 := by
                intro i
                simpa using ((hasDerivAt_id (0:ℝ)).mul_const (y i - w i)).const_add (w i)
              have e : g = fun t => P.alpha u * (w .m + t * (y .m - w .m)) / (1 - P.alpha u * (w .m + t * (y .m - w .m))) +
                P.beta u * (w .clet + t * (y .clet - w .clet)) + P.gamma u * (w .cloud + t * (y .cloud - w .cloud)) +
                P.delta u * (w .clet + t * (y .clet - w .clet)) / (1 - (1 / (P.n : ℝ)) * (P.delta u * (w .clet + t * (y .clet - w .clet)) + S))
                + z.2 * (P.delta u / (P.n : ℝ) * (w .clet + t * (y .clet - w .clet))) + α / 2 * (((w .m + t * (y .m - w .m)) - c.1 u .m) ^ 2 + ((w .clet + t * (y .clet - w .clet)) - c.1 u .clet) ^ 2 + ((w .cloud + t * (y .cloud - w .cloud)) - c.1 u .cloud) ^ 2) := by
                funext t
                simp only [hg, objF, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hSdef]
              rw [e]
              have hm := hl .m
              have hc := hl .clet
              have ho := hl .cloud
              have d1 := (hm.const_mul (P.alpha u)).div ((hm.const_mul (P.alpha u)).const_sub 1) (by simpa using hden1.ne')
              have d2 := hc.const_mul (P.beta u)
              have d3 := ho.const_mul (P.gamma u)
              have d4 := (hc.const_mul (P.delta u)).div ((((hc.const_mul (P.delta u)).add_const S).const_mul (1 / (P.n : ℝ))).const_sub 1) (by simpa using hden2.ne')
              have d5 := (hc.const_mul (P.delta u / (P.n : ℝ))).const_mul z.2
              have d6 := ((((hm.sub_const (c.1 u .m)).pow 2).add ((hc.sub_const (c.1 u .clet)).pow 2)).add ((ho.sub_const (c.1 u .cloud)).pow 2)).const_mul (α / 2)
              have d := ((((d1.add d2).add d3).add d4).add d5).add d6
              refine d.congr_deriv ?_
              have n1 := hden1.ne'
              have n2 := hden2.ne'
              simp only [zero_mul, add_zero]
              have E1 : (P.alpha u * (y .m - w .m) * (1 - P.alpha u * w .m) - P.alpha u * w .m * -(P.alpha u * (y .m - w .m))) / (1 - P.alpha u * w .m) ^ 2 = P.alpha u / (1 - P.alpha u * w .m) ^ 2 * (y .m - w .m) := by
                rw [div_mul_eq_mul_div]; congr 1; ring
              have E2 : (P.delta u * (y .clet - w .clet) * (1 - 1 / (P.n:ℝ) * (P.delta u * w .clet + S)) - P.delta u * w .clet * -(1 / (P.n:ℝ) * (P.delta u * (y .clet - w .clet)))) / (1 - 1 / (P.n:ℝ) * (P.delta u * w .clet + S)) ^ 2 = P.delta u * (1 - 1 / (P.n:ℝ) * S) / (1 - 1 / (P.n:ℝ) * (P.delta u * w .clet + S)) ^ 2 * (y .clet - w .clet) := by
                rw [div_mul_eq_mul_div]; congr 1; ring
              rw [E1, E2]
              norm_num
              ring
            have hlim := hder.tendsto_slope_zero_right
            have hge : 0 ≤ ((P.alpha u / (1 - P.alpha u * w .m) ^ 2 + 0 + α * (w .m - c.1 u .m)) * (y .m - w .m) + 
               (P.beta u + P.delta u * (1 - 1 / (P.n:ℝ) * S) / (1 - 1 / (P.n:ℝ) * (P.delta u * w .clet + S)) ^ 2 + z.2 * (P.delta u / (P.n:ℝ)) + α * (w .clet - c.1 u .clet)) * (y .clet - w .clet) + 
               (P.gamma u + 0 + α * (w .cloud - c.1 u .cloud)) * (y .cloud - w .cloud)) := by
              refine ge_of_tendsto hlim ?_
              have : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT one_pos
              filter_upwards [this] with t ht
              have hmem : w + t • (y - w) ∈ Ktil P u := (ktilConvex P u).add_smul_sub_mem hw hy ⟨ht.1.le, ht.2.le⟩
              have h1 := hmin _ hmem
              have h2 : g 0 ≤ g (0 + t) := by
                simp only [hg, zero_smul, add_zero, zero_add, objF]
                exact h1
              rw [smul_eq_mul]
              exact mul_nonneg (inv_nonneg.2 ht.1.le) (by linarith)
            simpa using hge
          have objCont : ∀ {N : ℕ} (P : Params N) (hA : P.AssumptionA) 
                 (hD : ∀ x ∈ Kprod P, load P x < 1) (α : ℝ) (c z : (Fin N → Exist.Tier → ℝ) × ℝ) (hz : z.1 ∈ Kprod P) (u : Fin N),
              ContinuousOn (alg2Obj P α c z u) (Ktil P u) := by
            clear hA hS hD hM lemA lemB sumT ktilClosed ktilConvex kprodCompact kprodConvex keClosed keConvex lipF lipFe foc P
            intro N P hA hD α c z hz u
            have e : alg2Obj P α c z u = fun y => _ := funext fun y => objF P α c z u y
            rw [e]
            have h1 : ∀ y ∈ Ktil P u, 1 - P.alpha u * y .m ≠ 0 := fun y hy => by
              have := le1 P hA _ (updK P z.1 hz u y hy) u
              rw [Function.update_self] at this
              exact this.ne'
            have h2 : ∀ y ∈ Ktil P u, 1 - (1 / (P.n : ℝ)) * (P.delta u * y .clet + ∑ v ∈ Finset.univ.erase u, P.delta v * z.1 v .clet) ≠ 0 := fun y hy => by
              have := hD _ (updK P z.1 hz u y hy)
              rw [loadU] at this
              exact (by linarith : (0:ℝ) < _).ne'
            refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add (ContinuousOn.add (ContinuousOn.add (ContinuousOn.div (by fun_prop) (by fun_prop) h1) (by fun_prop)) (by fun_prop)) (ContinuousOn.div (by fun_prop) (by fun_prop) h2)) (by fun_prop)) (by fun_prop)
          have psiEx : ∀ (N : ℕ),
              ∃ ψ : EuclideanSpace ℝ ((Fin N × Exist.Tier) ⊕ Unit) ≃L[ℝ] ((Fin N → Exist.Tier → ℝ) × ℝ), ∀ a b, pairE (ψ a) (ψ b) = inner ℝ a b := by
            clear hA hS hD hM lemA lemB sumT ktilClosed ktilConvex kprodCompact kprodConvex keClosed keConvex le1 lipF lipFe updK loadU objF foc objCont P
            intro N
            let ψ : EuclideanSpace ℝ ((Fin N × Exist.Tier) ⊕ Unit) ≃ₗ[ℝ] ((Fin N → Exist.Tier → ℝ) × ℝ) :=
              { toFun := fun a => (fun u i => a (Sum.inl (u, i)), a (Sum.inr ()))
                map_add' := fun a b => rfl
                map_smul' := fun r a => rfl
                invFun := fun p => WithLp.toLp 2 (Sum.elim (fun ui => p.1 ui.1 ui.2) (fun _ => p.2))
                left_inv := fun a => by ext i; rcases i with ⟨u, i⟩ | ⟨⟩ <;> rfl
                right_inv := fun p => rfl }
            refine ⟨ψ.toContinuousLinearEquiv, fun a b => ?_⟩
            change pairE (ψ a) (ψ b) = _
            rw [PiLp.inner_apply, Fintype.sum_sum_type, Fintype.sum_prod_type]
            change (∑ u, ∑ i, a (Sum.inl (u, i)) * b (Sum.inl (u, i))) + a (Sum.inr ()) * b (Sum.inr ()) = _
            simp [mul_comm]
          have reg : ∀ {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
                 (hD : ∀ x ∈ Kprod P, load P x < 1) (hM : IsMonotoneOnE (Ke P) (Fe P)) (α : ℝ) (hα : 0 < α) (c : (Fin N → Exist.Tier → ℝ) × ℝ) (hne : (Ke P).Nonempty),
              ∃! p, IsVISolE (Ke P) (regMap P α c) p := by
            clear hA hS hD hM lemB sumT ktilClosed ktilConvex kprodCompact kprodConvex le1 lipF updK loadU objF foc objCont P
            intro N P hA hS hD hM α hα c hne
            obtain ⟨L, hL0, hL, -⟩ := lipFe P hA hS hD
            obtain ⟨ψ, hψ⟩ := psiEx N
            obtain ⟨B1, hB10, hB1⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖ψ x‖ ≤ B * ‖x‖ :=
              ⟨_, norm_nonneg _, fun x => ContinuousLinearMap.le_opNorm (ψ.toContinuousLinearMap) x⟩
            obtain ⟨B2, hB20, hB2⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖ψ.symm x‖ ≤ B * ‖x‖ :=
              ⟨_, norm_nonneg _, fun x => ContinuousLinearMap.le_opNorm (ψ.symm.toContinuousLinearMap) x⟩
            have he : ∀ x y, ψ.symm (regMap P α c (ψ x)) - ψ.symm (regMap P α c (ψ y)) = ψ.symm (Fe P (ψ x) - Fe P (ψ y)) + α • (x - y) := by
              intro x y
              apply ψ.injective
              simp only [regMap, map_sub, map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply, smul_sub]
              abel
            have h := lemA _ (ψ ⁻¹' (Ke P)) (hne.preimage ψ.surjective) ((keClosed P).preimage ψ.continuous)
              ((keConvex P).linear_preimage ψ.toLinearMap) (fun h => ψ.symm (regMap P α c (ψ h))) α
              (B2 * (L * B1) + α) hα ?_ ?_
            · obtain ⟨x, ⟨hx, hx2⟩, hu⟩ := h
              refine ⟨ψ x, ⟨hx, fun p hp => ?_⟩, fun p hp => ?_⟩
              · have := hx2 (ψ.symm p) (by simpa using hp)
                rw [← hψ] at this
                simpa using this
              · have := hu (ψ.symm p) ⟨by simpa using hp.1, fun y hy => ?_⟩
                · rw [← this]; simp
                · rw [← hψ]
                  have := hp.2 (ψ y) hy
                  simpa using this
            · intro x hx y hy
              have e := he x y
              rw [e]
              refine (norm_add_le _ _).trans ?_
              rw [add_mul]
              gcongr
              · calc ‖ψ.symm (Fe P (ψ x) - Fe P (ψ y))‖ ≤ B2 * ‖Fe P (ψ x) - Fe P (ψ y)‖ := hB2 _
                  _ ≤ B2 * (L * ‖ψ x - ψ y‖) := by
                    gcongr; exact hL _ hx _ hy
                  _ ≤ B2 * (L * (B1 * ‖x - y‖)) := by
                    gcongr
                    rw [← map_sub]
                    exact hB1 _
                  _ = _ := by ring
              · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα]
            · intro x hx y hy
              have e := he x y
              simp only [e]
              rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, ← hψ]
              have := hM _ hy _ hx
              simp only [ContinuousLinearEquiv.apply_symm_apply, map_sub]
              linarith
          have feCont : ∀ {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
                 (hD : ∀ x ∈ Kprod P, load P x < 1),
              ContinuousOn (Fe P) (Ke P) := by
            clear hA hS hD hM lemA lemB sumT ktilClosed ktilConvex kprodCompact kprodConvex keClosed keConvex le1 lipF updK loadU objF foc objCont psiEx reg P
            intro N P hA hS hD
            obtain ⟨L, hL0, hL, -⟩ := lipFe P hA hS hD
            have : LipschitzOnWith ⟨L, hL0⟩ (Fe P) (Ke P) := LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
              rw [dist_eq_norm, dist_eq_norm]; exact hL x hx y hy
            exact this.continuousOn
          have alg1 : ∀ {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
                 (hD : ∀ x ∈ Kprod P, load P x < 1) (hM : IsMonotoneOnE (Ke P) (Fe P)) (α : ℝ) (hα : 0 < α) 
                 (z) (hz : IsVISolE (Ke P) (Fe P) z) (t) (ht : IsAlg1Run P α t),
              ∃ z, IsVISolE (Ke P) (Fe P) z ∧ Tendsto t atTop (𝓝 z) := by
            clear hA hS hD hM lemA sumT ktilClosed ktilConvex kprodCompact kprodConvex keConvex le1 lipF lipFe updK loadU objF foc objCont reg P
            intro N P hA hS hD hM α hα z hz t ht
            obtain ⟨ψ, hψ⟩ := psiEx N
            have h := lemB _ (ψ ⁻¹' (Ke P)) ((keClosed P).preimage ψ.continuous) (fun h => ψ.symm (Fe P (ψ h)))
              (ψ.symm.continuous.comp_continuousOn ((feCont P hA hS hD).comp ψ.continuous.continuousOn (fun x hx => hx)))
              (fun x hx y hy => by
                rw [← hψ]; simpa using hM _ hy _ hx) (ψ.symm z) (by simpa using hz.1) (fun y hy => by
                rw [← hψ]; simpa using hz.2 _ hy) α hα (fun k => ψ.symm (t k)) (fun k => ⟨by simpa using (ht.2 k).1, fun y hy => by
                rw [← hψ]; simpa [regMap] using (ht.2 k).2 _ hy⟩)
            obtain ⟨x, hx, hx2, hx3⟩ := h
            refine ⟨ψ x, ⟨hx, fun p hp => ?_⟩, ?_⟩
            · have := hx2 (ψ.symm p) (by simpa using hp)
              rw [← hψ] at this
              simpa using this
            · have := (ψ.continuous.tendsto x).comp hx3
              simpa [Function.comp_def] using this
          have exSol : ∀ {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
                 (hD : ∀ x ∈ Kprod P, load P x < 1) (hM : IsMonotoneOnE (Ke P) (Fe P)) (hne : (Ke P).Nonempty),
              ∃ z, IsVISolE (Ke P) (Fe P) z := by
            clear hA hS hD hM lemA lemB sumT ktilClosed ktilConvex kprodConvex keClosed keConvex le1 lipF lipFe updK loadU objF foc objCont alg1 P
            intro N P hA hS hD hM hne
            obtain ⟨p0, hp0⟩ := hne
            obtain ⟨xh, hxh, hl⟩ : ∃ xh ∈ Kprod P, load P xh = 0 := by
              refine ⟨fun u i => match i with
                | .m => p0.1 u .m
                | .clet => 0
                | .cloud => p0.1 u .clet + p0.1 u .cloud, fun u => ?_, by simp [load]⟩
              obtain ⟨h0, h1, h2, h3⟩ := hp0.1 u
              refine ⟨fun i => ?_, ?_, ?_, ?_⟩
              · cases i
                · exact h0 _
                · exact le_rfl
                · exact add_nonneg (h0 _) (h0 _)
              · simp only []; linarith
              · simp only []; linarith
              · simpa using h3
            have hph : ((xh, 0) : (Fin N → Exist.Tier → ℝ) × ℝ) ∈ Ke P := ⟨hxh, le_rfl⟩
            have hpc : Continuous fun a : ((Fin N → Exist.Tier → ℝ) × ℝ) × ((Fin N → Exist.Tier → ℝ) × ℝ) => pairE a.1 a.2 := by
              unfold pairE Exist.pair; fun_prop
            obtain ⟨M, hMb⟩ : ∃ M : ℝ, ∀ x ∈ Kprod P, Exist.pair (Fe P (xh, 0)).1 (xh - x) ≤ M := by
              have hc : Continuous fun x => Exist.pair (Fe P (xh, 0)).1 (xh - x) := by
                unfold Exist.pair; fun_prop
              obtain ⟨M, hM⟩ := (kprodCompact P).bddAbove_image hc.continuousOn
              exact ⟨M, fun x hx => hM ⟨x, hx, rfl⟩⟩
            have hex : ∀ n : ℕ, ∃ p, IsVISolE (Ke P) (regMap P (1 / ((n:ℝ) + 1)) 0) p := fun n =>
              (reg P hA hS hD hM _ (by positivity) 0 ⟨p0, hp0⟩).exists
            choose p hp using hex
            obtain ⟨ψ, hψ⟩ := psiEx N
            have hlin : ∀ a b c : (Fin N → Exist.Tier → ℝ) × ℝ, pairE (a + b) c = pairE a c + pairE b c := by
              intro a b c
              rw [← ψ.apply_symm_apply a, ← ψ.apply_symm_apply b, ← ψ.apply_symm_apply c, ← map_add, hψ, hψ, hψ, inner_add_left]
            have hsm : ∀ (r : ℝ) (a c : (Fin N → Exist.Tier → ℝ) × ℝ), pairE (r • a) c = r * pairE a c := by
              intro r a c
              rw [← ψ.apply_symm_apply a, ← ψ.apply_symm_apply c, ← map_smul, hψ, hψ, real_inner_smul_left]
            have hcs : ∀ a b : (Fin N → Exist.Tier → ℝ) × ℝ, pairE a (b - a) ≤ pairE b b := by
              intro a b
              rw [← ψ.apply_symm_apply a, ← ψ.apply_symm_apply b, ← map_sub, hψ, hψ, inner_sub_right]
              have h := real_inner_self_nonneg (F := EuclideanSpace ℝ ((Fin N × Exist.Tier) ⊕ Unit)) (x := ψ.symm a - ψ.symm b)
              have h2 := real_inner_self_nonneg (F := EuclideanSpace ℝ ((Fin N × Exist.Tier) ⊕ Unit)) (x := ψ.symm b)
              have h3 := real_inner_self_nonneg (F := EuclideanSpace ℝ ((Fin N × Exist.Tier) ⊕ Unit)) (x := ψ.symm a)
              simp only [inner_sub_left, inner_sub_right] at h
              rw [real_inner_comm (ψ.symm a) (ψ.symm b)] at h
              linarith
            have hB0 : 0 ≤ pairE ((xh, 0) : (Fin N → Exist.Tier → ℝ) × ℝ) (xh, 0) := by
              rw [← ψ.apply_symm_apply ((xh, 0) : (Fin N → Exist.Tier → ℝ) × ℝ), hψ]
              exact real_inner_self_nonneg
            have hU := hA.1
            have hbd : ∀ n, (p n).2 ∈ Set.Icc 0 ((M + pairE ((xh, 0) : (Fin N → Exist.Tier → ℝ) × ℝ) (xh, 0)) / P.Umax) := by
              intro n
              refine ⟨(hp n).1.2, ?_⟩
              rw [le_div_iff₀ hU]
              have h1 := (hp n).2 _ hph
              have h2 := hM _ (hp n).1 _ hph
              have h3 := hcs (p n) (xh, 0)
              have h4 := hMb _ (hp n).1.1
              simp only [regMap, sub_zero] at h1
              rw [hlin, hsm] at h1
              rw [sub_eq_add_neg (Fe P (xh,0)), hlin, ← neg_one_smul ℝ (Fe P (p n)), hsm] at h2
              have h5 : pairE (Fe P (xh, 0)) ((xh, 0) - p n) = Exist.pair (Fe P (xh, 0)).1 (xh - (p n).1) - P.Umax * (p n).2 := by
                simp only [pairE, Fe, hl, Prod.fst_sub, Prod.snd_sub]; ring
              have h6 : (1 / ((n:ℝ) + 1)) ≤ 1 := by
                rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
              have h7 : (0:ℝ) < (1 / ((n:ℝ) + 1)) := by positivity
              have h8 : (1 / ((n:ℝ) + 1)) * pairE (p n) ((xh, 0) - p n) ≤ pairE ((xh, 0) : (Fin N → Exist.Tier → ℝ) × ℝ) (xh, 0) :=
                calc _ ≤ (1 / ((n:ℝ) + 1)) * pairE ((xh, 0) : (Fin N → Exist.Tier → ℝ) × ℝ) (xh, 0) := by gcongr
                  _ ≤ _ := mul_le_of_le_one_left hB0 h6
              linarith
            obtain ⟨z, hz, φ, hφ, hlim⟩ := ((kprodCompact P).prod isCompact_Icc).tendsto_subseq (x := p) (fun n => ⟨(hp n).1.1, hbd n⟩)
            have hzK : z ∈ Ke P := ⟨hz.1, hz.2.1⟩
            refine ⟨z, hzK, fun q hq => ?_⟩
            have hFl : Tendsto (fun n => Fe P (p (φ n))) atTop (𝓝 (Fe P z)) :=
              (feCont P hA hS hD z hzK).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => (hp _).1⟩)
            have heps : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
              tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
            have hreg : Tendsto (fun n => regMap P (1 / ((φ n : ℝ) + 1)) 0 (p (φ n))) atTop (𝓝 (Fe P z + (0:ℝ) • (z - 0))) :=
              hFl.add (heps.smul (hlim.sub_const 0))
            rw [zero_smul, add_zero] at hreg
            have := (hpc.tendsto (Fe P z, q - z)).comp (hreg.prodMk_nhds (tendsto_const_nhds.sub hlim))
            exact ge_of_tendsto' this fun n => (hp (φ n)).2 q hq
          have stepK : ∀ {N : ℕ} (P : Params N) (α : ℝ) (c z z' : (Fin N → Exist.Tier → ℝ) × ℝ) (h : IsAlg2Step P α c z z'),
              z' ∈ Ke P := by
            clear hA hS hD hM lemA lemB sumT ktilClosed ktilConvex kprodCompact kprodConvex keClosed keConvex le1 lipF lipFe updK loadU objF foc objCont psiEx reg feCont alg1 exSol P
            intro N P α c z z' h
            exact ⟨fun u => (h.1 u).1, by rw [h.2]; exact le_max_left _ _⟩
          have sqLe : ∀ (v w : Exist.Tier → ℝ),
              ‖v - w‖ ^ 2 ≤ ∑ i, (v i - w i) ^ 2 := by
            clear hA hS hD hM lemA lemB sumT ktilClosed ktilConvex kprodCompact kprodConvex keClosed keConvex le1 lipF lipFe updK loadU objF foc objCont psiEx reg feCont alg1 exSol stepK P
            intro v w
            have h : ‖v - w‖ ≤ Real.sqrt (∑ i, (v i - w i) ^ 2) := by
              rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
              intro i
              rw [Real.norm_eq_abs]
              refine Real.abs_le_sqrt ?_
              exact Finset.single_le_sum (f := fun i => (v i - w i) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
            calc ‖v - w‖ ^ 2 ≤ Real.sqrt (∑ i, (v i - w i) ^ 2) ^ 2 := by gcongr
              _ = _ := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
          have alg2Ex : ∀ {N : ℕ} (P : Params N) (hA : P.AssumptionA)
                 (hD : ∀ x ∈ Kprod P, load P x < 1) (hM : IsMonotoneOnE (Ke P) (Fe P)) (α : ℝ) (hα : 0 < α) (c z) (hz : z ∈ Ke P),
              ∃! z', IsAlg2Step P α c z z' := by
            clear hA hS hD hM lemA lemB ktilConvex kprodCompact kprodConvex keClosed keConvex le1 lipF lipFe loadU objF psiEx reg feCont alg1 exSol stepK P
            intro N P hA hD hM α hα c z hz
            have hex : ∀ u, ∃ w ∈ Ktil P u, ∀ y ∈ Ktil P u, alg2Obj P α c z u w ≤ alg2Obj P α c z u y := fun u =>
              (ktilClosed P u).exists_isMinOn ⟨_, hz.1 u⟩ (objCont P hA hD α c z hz.1 u)
            choose w hw1 hw2 using hex
            refine ⟨(w, alg2Price P α c z), ⟨fun u => ⟨hw1 u, hw2 u⟩, rfl⟩, ?_⟩
            rintro ⟨v, r⟩ ⟨hv, hr⟩
            refine Prod.ext ?_ hr
            funext u
            obtain ⟨hv1, hv2⟩ := hv u
            simp only at hv1 hv2 ⊢
            have f1 := foc P hA hD α c z hz.1 u _ (hw1 u) (hw2 u) _ hv1
            have f2 := foc P hA hD α c z hz.1 u _ hv1 hv2 _ (hw1 u)
            have m := hM (Function.update z.1 u (w u), z.2) ⟨updK P z.1 hz.1 u _ (hw1 u), hz.2⟩ (Function.update z.1 u (v u), z.2) ⟨updK P z.1 hz.1 u _ hv1, hz.2⟩
            have e : pairE (Fe P (Function.update z.1 u (v u), z.2) - Fe P (Function.update z.1 u (w u), z.2)) 
              ((Function.update z.1 u (v u), z.2) - (Function.update z.1 u (w u), z.2)) = ∑ i, ((Fe P (Function.update z.1 u (v u), z.2)).1 u i - (Fe P (Function.update z.1 u (w u), z.2)).1 u i) * (v u i - w u i) := by
              simp only [pairE, Exist.pair, Prod.fst_sub, Prod.snd_sub, sub_self, mul_zero, add_zero, Pi.sub_apply]
              rw [Finset.sum_eq_single u]
              · simp
              · intro b _ hb
                simp [Function.update_of_ne hb]
              · simp
            rw [e] at m
            have hs := sqLe (v u) (w u)
            simp only [sumT] at f1 f2 m hs
            have : α * ‖v u - w u‖ ^ 2 ≤ 0 := by
              have := mul_le_mul_of_nonneg_left hs hα.le
              linarith
            have h0 : ‖v u - w u‖ ^ 2 ≤ 0 := by
              by_contra hc
              push Not at hc
              have := mul_pos hα hc
              linarith
            have h1 : ‖v u - w u‖ = 0 := (pow_eq_zero_iff two_ne_zero).1 (le_antisymm h0 (sq_nonneg _))
            exact sub_eq_zero.1 (norm_eq_zero.1 h1)
          have contr : ∀ {N : ℕ} (P : Params N) (hA : P.AssumptionA) 
                 (hD : ∀ x ∈ Kprod P, load P x < 1) (L : ℝ) (hL0 : 0 ≤ L) (hL : ∀ p ∈ Ke P, ∀ q ∈ Ke P, ‖Fe P p - Fe P q‖ ≤ L * ‖p - q‖) (hL2 : ∀ x ∈ Kprod P, ∀ y ∈ Kprod P, |load P x - load P y| ≤ L * ‖x - y‖)
                 (α : ℝ) (hα : 9 * L + 1 < α) (c z z' p) (hz : z ∈ Ke P) (hs : IsAlg2Step P α c z z') (hp : IsVISolE (Ke P) (regMap P α c) p),
              ‖z' - p‖ ≤ 1 / 2 * ‖z - p‖ := by
            clear hA hS hD hM lemA lemB ktilClosed ktilConvex kprodCompact kprodConvex keClosed keConvex le1 lipF lipFe loadU objF objCont psiEx reg feCont alg1 exSol stepK alg2Ex P
            intro N P hA hD L hL0 hL hL2 α hα c z z' p hz hs hp
            have hα0 : 0 < α := by linarith
            have hR : 0 ≤ 1 / 2 * ‖z - p‖ := by positivity
            rw [Prod.norm_def, max_le_iff]
            constructor
            · rw [Prod.fst_sub, pi_norm_le_iff_of_nonneg hR]
              intro u
              obtain ⟨hw, hmin⟩ := hs.1 u
              have f1 := foc P hA hD α c z hz.1 u _ hw hmin _ (hp.1.1 u)
              have f2 := hp.2 (Function.update p.1 u (z'.1 u), p.2) ⟨updK P p.1 hp.1.1 u _ hw, hp.1.2⟩
              have e : pairE (regMap P α c p) ((Function.update p.1 u (z'.1 u), p.2) - p) = ∑ i, ((Fe P p).1 u i + α * (p.1 u i - c.1 u i)) * (z'.1 u i - p.1 u i) := by
                simp only [pairE, Exist.pair, regMap, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.smul_fst, sub_self, mul_zero, add_zero, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
                rw [Finset.sum_eq_single u]
                · simp
                · intro b _ hb
                  simp [Function.update_of_ne hb]
                · simp
              rw [e] at f2
              set q : (Fin N → Exist.Tier → ℝ) × ℝ := (Function.update z.1 u (z'.1 u), z.2) with hq
              have hqK : q ∈ Ke P := ⟨updK P z.1 hz.1 u _ hw, hz.2⟩
              have hlip := hL _ hp.1 _ hqK
              set a := ‖z'.1 u - p.1 u‖ with ha
              set d := ‖z - p‖ with hd
              have ha0 : 0 ≤ a := norm_nonneg _
              have hd0 : 0 ≤ d := norm_nonneg _
              have hpq : ‖p - q‖ ≤ d + a := by
                rw [Prod.norm_def, max_le_iff]
                constructor
                · rw [Prod.fst_sub, pi_norm_le_iff_of_nonneg (by positivity)]
                  intro v
                  by_cases h : v = u
                  · subst h
                    simp only [hq, Pi.sub_apply, Function.update_self]
                    rw [norm_sub_rev]
                    linarith
                  · simp only [hq, Pi.sub_apply, Function.update_of_ne h]
                    have h1 : ‖(z.1 - p.1) v‖ ≤ ‖z.1 - p.1‖ := norm_le_pi_norm _ _
                    have h2 : ‖z.1 - p.1‖ ≤ d := norm_fst_le (z - p)
                    rw [norm_sub_rev]
                    simp only [Pi.sub_apply] at h1
                    linarith
                · have h2 : ‖z.2 - p.2‖ ≤ d := norm_snd_le (z - p)
                  rw [Prod.snd_sub, norm_sub_rev]
                  linarith
              have hB : ∀ i, ((Fe P p).1 u i - (Fe P q).1 u i) * (z'.1 u i - p.1 u i) ≤ L * (d + a) * a := by
                intro i
                have h1 : ‖(Fe P p).1 u i - (Fe P q).1 u i‖ ≤ L * (d + a) := 
                  calc _ ≤ ‖(Fe P p - Fe P q).1 u‖ := norm_le_pi_norm ((Fe P p - Fe P q).1 u) i
                    _ ≤ ‖(Fe P p - Fe P q).1‖ := norm_le_pi_norm _ u
                    _ ≤ ‖Fe P p - Fe P q‖ := norm_fst_le _
                    _ ≤ L * ‖p - q‖ := hlip
                    _ ≤ _ := by gcongr
                have h2 : ‖z'.1 u i - p.1 u i‖ ≤ a := norm_le_pi_norm (z'.1 u - p.1 u) i
                calc _ ≤ ‖((Fe P p).1 u i - (Fe P q).1 u i) * (z'.1 u i - p.1 u i)‖ := Real.le_norm_self _
                  _ ≤ _ := by rw [norm_mul]; gcongr
              have hsq := sqLe (z'.1 u) (p.1 u)
              rw [← ha] at hsq
              have b1 := hB .m
              have b2 := hB .clet
              have b3 := hB .cloud
              simp only [sumT] at f1 f2 hsq
              have k1 := mul_le_mul_of_nonneg_left hsq hα0.le
              have k2 : α * a ^ 2 ≤ 3 * (L * (d + a) * a) := by linear_combination k1 + f1 + f2 + b1 + b2 + b3
              change a ≤ 1 / 2 * d
              by_contra hc
              push Not at hc
              have ha1 : 0 < a := by linarith
              have k3 : α * a ≤ 3 * (L * (d + a)) :=
                le_of_mul_le_mul_right (by linear_combination k2) ha1
              have k4 : L * d ≤ L * (2 * a) := mul_le_mul_of_nonneg_left (by linarith) hL0
              have k5 := mul_lt_mul_of_pos_right hα ha1
              clear f1 f2 hsq b1 b2 b3 k1 k2 hB hlip hmin hpq
              linarith
            · have hl := hL2 _ hz.1 _ hp.1.1
              have n1 : ‖z.1 - p.1‖ ≤ ‖z - p‖ := norm_fst_le (z - p)
              have key : p.2 = max 0 (c.2 + 1 / α * (load P p.1 - P.Umax)) := by
                have t : ∀ r : ℝ, 0 ≤ r → 0 ≤ (-load P p.1 + P.Umax + α * (p.2 - c.2)) * (r - p.2) := by
                  intro r hr
                  have := hp.2 (p.1, r) ⟨hp.1.1, hr⟩
                  simpa [pairE, Exist.pair, regMap, Fe] using this
                have t1 := t (p.2 + 1) (by linarith [hp.1.2])
                have t0 := t 0 le_rfl
                have e : c.2 + 1 / α * (load P p.1 - P.Umax) = p.2 - (1 / α) * (-load P p.1 + P.Umax + α * (p.2 - c.2)) := by
                  have hinv : 1 / α * α = 1 := one_div_mul_cancel hα0.ne'
                  linear_combination (p.2 - c.2) * hinv
                rw [e]
                set v := -load P p.1 + P.Umax + α * (p.2 - c.2) with hv
                have hv0 : 0 ≤ v := by linarith
                have hp2 := hp.1.2
                have h1 : 0 ≤ 1 / α * v := by positivity
                rcases hp2.eq_or_lt with h | h
                · rw [max_eq_left (by rw [← h]; linarith)]; exact h.symm
                · have : v = 0 := by
                    by_contra hc
                    have : 0 < v := lt_of_le_of_ne hv0 (Ne.symm hc)
                    have := mul_pos this h
                    linarith
                  rw [this, mul_zero, sub_zero, max_eq_right h.le]
              rw [Prod.snd_sub, hs.2, alg2Price, Real.norm_eq_abs]
              nth_rewrite 1 [key]
              rw [max_comm 0, max_comm 0]
              refine (abs_max_sub_max_le_abs _ _ _).trans ?_
              have e : c.2 + 1 / α * (load P z.1 - P.Umax) - (c.2 + 1 / α * (load P p.1 - P.Umax)) = (load P z.1 - load P p.1) / α := by
                ring
              rw [e, abs_div, abs_of_pos hα0, div_le_iff₀ hα0]
              have h1 : L * ‖z.1 - p.1‖ ≤ L * ‖z - p‖ := by gcongr
              have h2 : L * ‖z - p‖ ≤ (α / 2) * ‖z - p‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
              linarith
          constructor
          · intro α hα
            have hα0 : 0 < α := by
              refine lt_of_le_of_lt ?_ hα
              have h1 : 0 ≤ deltaMax P := Real.iSup_nonneg fun u => (hA.2.2 u).2.2.1.le
              have h2 : 0 < 1 - P.Umax := by linarith [hA.2.1]
              unfold alphaBar
              positivity
            refine ⟨fun c hc => reg P hA hS hD hM α hα0 c ⟨c, hc⟩, fun c hc z hz => alg2Ex P hA hD hM α hα0 c z hz, fun t ht => ?_⟩
            obtain ⟨z, hz⟩ := exSol P hA hS hD hM ⟨_, ht.1⟩
            exact alg1 P hA hS hD hM α hα0 z hz t ht
          · obtain ⟨L, hL0, hL, hL2⟩ := lipFe P hA hS hD
            refine ⟨9 * L + 1, by positivity, fun α hα c hc s hs p hp => ?_⟩
            have hK : ∀ i, s i ∈ Ke P := by
              intro i
              cases i with
              | zero => exact hs.1
              | succ i => exact stepK P α c _ _ (hs.2 i)
            have hb : ∀ i, ‖s i - p‖ ≤ (1 / 2) ^ i * ‖s 0 - p‖ := by
              intro i
              induction i with
              | zero => simp
              | succ i ih =>
                have := contr P hA hD L hL0 hL hL2 α hα c _ _ p (hK i) (hs.2 i) hp
                rw [pow_succ]
                linarith
            rw [tendsto_iff_norm_sub_tendsto_zero]
            refine squeeze_zero (fun i => norm_nonneg _) hb ?_
            have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1/2:ℝ)) (by norm_num) (by norm_num)).mul_const ‖s 0 - p‖
            simpa using this
