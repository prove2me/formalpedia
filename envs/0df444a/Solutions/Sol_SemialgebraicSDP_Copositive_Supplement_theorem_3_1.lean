-- Prove2me | solution 1 for SemialgebraicSDP.Copositive.Supplement.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:32:19.483812+00:00
-- url     : https://prove2.me/submissions/f4e817a3-59e1-44fd-9db6-449cf61fbf4d

import Mathlib
import Definitions.Def_SemialgebraicSDP_Copositive_Supplement_SDPPair

open SemialgebraicSDP
open SemialgebraicSDP.Copositive
open SemialgebraicSDP.Copositive.Supplement

/-- Theorem 3.1, corrected: one strict side also requires feasibility of the other.
The second clause retains joint attainment under strict feasibility of both sides. -/
theorem solution {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (hA : ∀ i, (A i).IsSymm) (hC : C.IsSymm) :
    (((∃ X, PrimalFeasible A b X) ∧ (∃ y, DualFeasible A C y) ∧
        (PrimalStrict A b ∨ DualStrict A C)) →
      ∀ ε : ℝ, 0 < ε → ∃ X y, PrimalFeasible A b X ∧ DualFeasible A C y ∧
        tracePair C X - ∑ i, b i * y i < ε) ∧
    ((PrimalStrict A b ∧ DualStrict A C) →
      ∃ X y, PrimalFeasible A b X ∧ DualFeasible A C y ∧
        tracePair C X = ∑ i, b i * y i ∧
        (∀ Z, PrimalFeasible A b Z → tracePair C X ≤ tracePair C Z) ∧
        (∀ w, DualFeasible A C w → (∑ i, b i * w i) ≤ ∑ i, b i * y i)) := by
          classical
          letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) := Matrix.normedAddCommGroup
          letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := Matrix.normedSpace
          haveI : ProperSpace (Matrix (Fin n) (Fin n) ℝ) := FiniteDimensional.proper_real _
          have H1 : ∀ S X : Matrix (Fin n) (Fin n) ℝ, S.PosSemidef → X.PosSemidef → 0 ≤ tracePair S X := by
            intro S X hS hX
            open scoped MatrixOrder in
            have hX' : 0 ≤ X := Matrix.nonneg_iff_posSemidef.2 hX
            open scoped MatrixOrder in
            have hR : X = CFC.sqrt X * CFC.sqrt X := (CFC.sqrt_mul_sqrt_self X hX').symm
            open scoped MatrixOrder in
            have hRs : Matrix.conjTranspose (CFC.sqrt X) = CFC.sqrt X := (CFC.sqrt_nonneg X).isSelfAdjoint
            open scoped MatrixOrder in
            have key := hS.mul_mul_conjTranspose_same (CFC.sqrt X)
            open scoped MatrixOrder in
            (unfold tracePair; rw [hR, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
             nth_rewrite 2 [← hRs]; exact key.trace_nonneg)
          have H2 : ∀ S : Matrix (Fin n) (Fin n) ℝ, S.IsSymm →
              (∀ v : Fin n → ℝ, 0 ≤ tracePair S (Matrix.vecMulVec v v)) → S.PosSemidef := by
            intro S hS hv
            refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
            · simpa [Matrix.IsHermitian, Matrix.IsSymm] using hS
            · have := hv x
              refine this.trans_eq ?_
              simp only [tracePair, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
                dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
              rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              rw [show S j i = S i j from by simpa using congrFun (congrFun hS i) j]; ring
          have HC : IsClosed {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef} := by
            have : {X : Matrix (Fin n) (Fin n) ℝ | X.PosSemidef} =
                (⋂ i, ⋂ j, {p | p j i = p i j}) ∩
                  ⋂ x : Fin n → ℝ, {p | 0 ≤ ∑ i, ∑ j, x i * (p i j * x j)} := by
              ext p
              simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
                Matrix.posSemidef_iff_dotProduct_mulVec,
                Matrix.IsHermitian, dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
              constructor
              · rintro ⟨h1, h2⟩
                refine ⟨fun i j => ?_, fun x => h2 x⟩
                have := congrFun (congrFun h1 i) j
                simpa using this
              · rintro ⟨h1, h2⟩
                refine ⟨?_, fun x => h2 x⟩
                ext i j; simpa using h1 i j
            rw [this]
            refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j =>
              isClosed_eq (by fun_prop) (by fun_prop))
              (isClosed_iInter fun x => isClosed_le (by fun_prop) (by fun_prop))
          have Hlam : ∀ S : Matrix (Fin n) (Fin n) ℝ, S.PosDef →
              ∃ r : ℝ, 0 < r ∧ (S - r • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
            open scoped MatrixOrder in
            (intro S h
             rcases Nat.eq_zero_or_pos n with hn | hn
             · subst hn
               refine ⟨1, one_pos, ?_⟩
               rw [Subsingleton.elim (S - _) 0]; exact Matrix.PosSemidef.zero
             have : NeZero n := ⟨hn.ne'⟩
             have hs := h.isStrictlyPositive
             obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff hs.isSelfAdjoint).2
               fun x hx ↦ hs.spectrum_pos hx
             refine ⟨r, hr, ?_⟩
             rw [Matrix.le_iff] at hle
             simpa [Algebra.algebraMap_eq_smul_one] using hle)
          have Hcont : ∀ M : Matrix (Fin n) (Fin n) ℝ, Continuous fun X : Matrix (Fin n) (Fin n) ℝ =>
              tracePair M X := by
            intro M; unfold tracePair; exact (continuous_const.matrix_mul continuous_id).matrix_trace
          have Hlin : ∀ (M : Matrix (Fin n) (Fin n) ℝ) (y : Fin m → ℝ) X,
              tracePair (M - ∑ i, y i • A i) X = tracePair M X - ∑ i, y i * tracePair (A i) X := by
            intro M y X
            simp [tracePair, Matrix.sub_mul, Finset.sum_mul, Matrix.trace_sub, Matrix.trace_sum,
              Matrix.smul_mul, Matrix.trace_smul]
          have Hlam' : ∀ (S X : Matrix (Fin n) (Fin n) ℝ) (r : ℝ),
              tracePair (S - r • (1 : Matrix (Fin n) (Fin n) ℝ)) X = tracePair S X - r * X.trace := by
            intro S X r
            simp [tracePair, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul]
          have Hnorm : ∀ X : Matrix (Fin n) (Fin n) ℝ, X.PosSemidef → ‖X‖ ≤ X.trace := by
            intro X hX
            have htr : 0 ≤ X.trace := hX.trace_nonneg
            have hd : ∀ k, X k k ≤ X.trace := fun k => by
              unfold Matrix.trace
              exact Finset.single_le_sum (f := fun k => X.diag k) (fun k _ => hX.diag_nonneg)
                (Finset.mem_univ k)
            refine (Matrix.norm_le_iff htr).2 fun i j => ?_
            have hsym : X j i = X i j := by simpa using congrFun (congrFun hX.1 i) j
            have q1 := hX.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
            have q2 := hX.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
            simp [Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add, add_dotProduct, sub_dotProduct,
              dotProduct_sub, Matrix.mulVec_single_one] at q1 q2
            rw [Real.norm_eq_abs, abs_le]
            have := hd i; have := hd j
            constructor <;> nlinarith
          have weak : ∀ X y, PrimalFeasible A b X → DualFeasible A C y →
              ∑ i, b i * y i ≤ tracePair C X := by
            rintro X y ⟨hX, hXb⟩ hy
            have := H1 _ _ hy hX
            rw [Hlin] at this; simp only [hXb] at this
            have e : ∑ i, y i * b i = ∑ i, b i * y i := Finset.sum_congr rfl fun i _ => mul_comm _ _
            linarith
          have Hsymm : ∀ y : Fin m → ℝ, (C - ∑ i, y i • A i).IsSymm := by
            intro y; unfold Matrix.IsSymm; rw [Matrix.transpose_sub, Matrix.transpose_sum]
            simp [Matrix.transpose_smul, (hA _).eq, hC.eq]
          have closedImg : ∀ {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
              [NormedAddCommGroup W] (P : Set V) (h : V → W) (g : W → ℝ), IsClosed P →
              Continuous h → Continuous g → (∀ v ∈ P, ‖v‖ ≤ g (h v)) → IsClosed (h '' P) := by
            intro V W _ _ _ _ P h g hP hh hg hcoer
            refine isClosed_of_closure_subset fun w hw => ?_
            obtain ⟨x, hxP, hx⟩ := mem_closure_iff_seq_limit.1 hw
            choose v hvP hv using hxP
            have hgx : Filter.Tendsto (fun k => g (x k)) Filter.atTop (nhds (g w)) :=
              (hg.tendsto w).comp hx
            obtain ⟨R, hR⟩ := hgx.bddAbove_range
            have hb : ∀ k, v k ∈ Metric.closedBall (0 : V) R := fun k => by
              rw [Metric.mem_closedBall, dist_zero_right]
              exact (hcoer _ (hvP k)).trans (by rw [hv k]; exact hR ⟨k, rfl⟩)
            obtain ⟨v0, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0:V) R).tendsto_subseq hb
            have hv0 : v0 ∈ P := hP.mem_of_tendsto hlim (Filter.Eventually.of_forall fun k => hvP _)
            refine ⟨v0, hv0, ?_⟩
            have h1 : Filter.Tendsto (fun k => h (v (φ k))) Filter.atTop (nhds (h v0)) :=
              (hh.tendsto v0).comp hlim
            have h2 : Filter.Tendsto (fun k => h (v (φ k))) Filter.atTop (nhds w) := by
              simp only [hv]; exact hx.comp hφ.tendsto_atTop
            exact tendsto_nhds_unique h1 h2
          have cone : ∀ (f u : ℝ), u < 0 → (∀ a : ℝ, 0 < a → u < a * f) → 0 ≤ f := by
            intro f u hu h; by_contra hf; push_neg at hf
            have := h (u / f) (div_pos_of_neg_of_neg hu hf)
            rw [div_mul_cancel₀ _ hf.ne] at this; exact lt_irrefl _ this
          have HtpAdd : ∀ M X Y : Matrix (Fin n) (Fin n) ℝ, tracePair M (X + Y) = tracePair M X + tracePair M Y := by
            intro M X Y; simp [tracePair, Matrix.mul_add, Matrix.trace_add]
          have HtpSmul : ∀ (M X : Matrix (Fin n) (Fin n) ℝ) (a : ℝ), tracePair M (a • X) = a * tracePair M X := by
            intro M X a; simp [tracePair, Matrix.mul_smul, Matrix.trace_smul]
          have HvvPSD : ∀ v : Fin n → ℝ, (Matrix.vecMulVec v v).PosSemidef := fun v => by
            simpa using Matrix.posSemidef_vecMulVec_self_star v
          have DS : DualStrict A C → (∃ X, PrimalFeasible A b X) →
              ∃ X, PrimalFeasible A b X ∧ (∀ Z, PrimalFeasible A b Z → tracePair C X ≤ tracePair C Z) ∧
                ∀ δ > 0, ∃ y, DualFeasible A C y ∧ tracePair C X - δ < ∑ i, b i * y i := by
            rintro ⟨y0, hy0⟩ ⟨X1, hX1⟩
            obtain ⟨lam, hlam, hS0⟩ := Hlam _ hy0
            let h : Matrix (Fin n) (Fin n) ℝ × ℝ → (Fin m → ℝ) × ℝ :=
              fun p => (fun i => tracePair (A i) p.1, tracePair C p.1 + p.2)
            let P : Set (Matrix (Fin n) (Fin n) ℝ × ℝ) := {p | p.1.PosSemidef ∧ 0 ≤ p.2}
            have hK : IsClosed (h '' P) := by
              refine closedImg P h (fun q => (1/lam + 1) * (q.2 - ∑ i, y0 i * q.1 i)) ?_ ?_ ?_ ?_
              · exact (HC.preimage continuous_fst).inter (isClosed_le continuous_const continuous_snd)
              · refine Continuous.prodMk (continuous_pi fun i => (Hcont _).comp continuous_fst) ?_
                exact ((Hcont _).comp continuous_fst).add continuous_snd
              · fun_prop
              · rintro ⟨X, r⟩ ⟨hX, hr⟩
                have e1 := H1 _ _ hS0 hX
                rw [Hlam', Hlin] at e1
                have hn := Hnorm X hX
                have hlx : lam * X.trace ≤ tracePair C X - ∑ i, y0 i * tracePair (A i) X := by linarith
                have htx : X.trace ≤ (tracePair C X - ∑ i, y0 i * tracePair (A i) X) / lam := by
                  rw [le_div_iff₀ hlam]; linarith
                set a := tracePair C X - ∑ i, y0 i * tracePair (A i) X
                have ha : 0 ≤ a := by nlinarith [hX.trace_nonneg]
                have hq : (1/lam + 1) * (tracePair C X + r - ∑ i, y0 i * tracePair (A i) X)
                    = a / lam + a + r / lam + r := by simp only [a]; field_simp; ring
                show ‖(X, r)‖ ≤ (1/lam + 1) * (tracePair C X + r - ∑ i, y0 i * tracePair (A i) X)
                rw [hq, norm_prod_le_iff]
                have : 0 ≤ r / lam := div_nonneg hr hlam.le
                have : 0 ≤ a / lam := div_nonneg ha hlam.le
                refine ⟨by simp only; linarith, ?_⟩
                simp only [Real.norm_eq_abs, abs_of_nonneg hr]; linarith
            have hKconv : Convex ℝ (h '' P) := by
              rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a c ha hc hac
              refine ⟨a • p + c • q, ⟨?_, ?_⟩, ?_⟩
              · exact (hp.1.smul ha).add (hq.1.smul hc)
              · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; nlinarith [hp.2, hq.2]
              · ext i
                · simp only [h, Prod.fst_add, Prod.smul_fst, HtpAdd, HtpSmul, Prod.smul_mk, Prod.mk_add_mk,
                    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
                · simp only [h, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, HtpAdd, HtpSmul,
                    Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]; ring
            let T : Set ℝ := {t | ((fun i => b i), t) ∈ h '' P}
            have hTc : IsClosed T := hK.preimage (by fun_prop)
            have hX1T : tracePair C X1 ∈ T := ⟨(X1, 0), ⟨hX1.1, le_refl _⟩, by simp [h, hX1.2]⟩
            have hTb : BddBelow T := ⟨∑ i, b i * y0 i, by
              rintro t ⟨⟨X, r⟩, ⟨hX, hr⟩, he⟩
              simp only [h, Prod.mk.injEq] at he
              have hpf : PrimalFeasible A b X := ⟨hX, fun i => congrFun he.1 i⟩
              have := weak X y0 hpf hy0.posSemidef
              simp only at hr
              linarith [he.2]⟩
            have htmem := hTc.csInf_mem ⟨_, hX1T⟩ hTb
            set ts := sInf T
            obtain ⟨⟨Xs, rs⟩, ⟨hXs, hrs⟩, hes⟩ := htmem
            simp only [h, Prod.mk.injEq] at hes
            simp only at hXs hrs
            have hXsF : PrimalFeasible A b Xs := ⟨hXs, fun i => congrFun hes.1 i⟩
            have hmin : ∀ Z, PrimalFeasible A b Z → ts ≤ tracePair C Z := fun Z hZ =>
              csInf_le hTb ⟨(Z, 0), ⟨hZ.1, le_rfl⟩, by simp [h, hZ.2]⟩
            refine ⟨Xs, hXsF, fun Z hZ => by linarith [hmin Z hZ], fun δ hδ => ?_⟩
            have hnot : ((fun i => b i), ts - δ) ∉ h '' P := fun hin => by
              have := csInf_le hTb hin; linarith
            obtain ⟨f, u, hfu, hfK⟩ := geometric_hahn_banach_point_closed hKconv hK hnot
            set η : Fin m → ℝ := fun i => f (Pi.single i 1, 0) with hη
            set s := f (0, 1) with hs
            have hrep : ∀ (v : Fin m → ℝ) (t : ℝ), f (v, t) = ∑ i, v i * η i + t * s := by
              intro v t
              have e1 : (v, t) = ((v, 0) : (Fin m → ℝ) × ℝ) + t • ((0 : Fin m → ℝ), (1:ℝ)) := by simp
              have e2 : ((v, 0) : (Fin m → ℝ) × ℝ) = ∑ i, v i • ((Pi.single i 1 : Fin m → ℝ), (0:ℝ)) := by
                refine Prod.ext ?_ ?_
                · rw [Prod.fst_sum]; ext j; simp [Finset.sum_apply, Pi.single_apply]
                · rw [Prod.snd_sum]; simp
              rw [e1, e2, map_add, map_sum, map_smul]; simp only [map_smul, smul_eq_mul, η, s]
            have h0K : ((0 : Fin m → ℝ), (0:ℝ)) ∈ h '' P :=
              ⟨(0, 0), ⟨Matrix.PosSemidef.zero, le_rfl⟩, by simp [h, tracePair]; rfl⟩
            have hu : u < 0 := by have := hfK _ h0K; rwa [Prod.mk_zero_zero, map_zero] at this
            have hnn : ∀ p ∈ P, 0 ≤ f (h p) := by
              intro p hp
              refine cone _ u hu fun a ha => ?_
              have hmem : h (a • p) ∈ h '' P := ⟨_, ⟨hp.1.smul ha.le, by
                simp only [Prod.smul_snd, smul_eq_mul]; exact mul_nonneg ha.le hp.2⟩, rfl⟩
              have e : h (a • p) = a • h p := by
                ext i
                · simp [h, HtpSmul]
                · simp [h, HtpSmul]; ring
              have := hfK _ hmem
              rwa [e, map_smul, smul_eq_mul] at this
            have hs0 : 0 ≤ s := by
              have := hnn (0, 1) ⟨Matrix.PosSemidef.zero, zero_le_one⟩
              simpa [h, hrep, tracePair] using this
            have hk := hnn (Xs, rs) ⟨hXs, hrs⟩
            simp only [h, hrep, hes.1] at hk
            rw [hes.2] at hk
            rw [hrep] at hfu
            have hspos : 0 < s := by
              by_contra hneg; push_neg at hneg
              have : s = 0 := le_antisymm hneg hs0
              rw [this] at hk hfu; simp at hk hfu; linarith
            let y : Fin m → ℝ := fun i => -η i / s
            have hsum : ∀ v : Fin m → ℝ, ∑ i, y i * v i = -(∑ i, v i * η i) / s := by
              intro v
              rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
              refine Finset.sum_congr rfl fun i _ => ?_; simp only [y]; ring
            refine ⟨y, ?_, ?_⟩
            · refine H2 _ (Hsymm y) fun v => ?_
              have hv := hnn (Matrix.vecMulVec v v, 0) ⟨HvvPSD v, le_rfl⟩
              simp only [h, hrep, add_zero] at hv
              rw [Hlin, hsum (fun i => tracePair (A i) (Matrix.vecMulVec v v))]
              have : tracePair C (Matrix.vecMulVec v v) -
                  -(∑ i, tracePair (A i) (Matrix.vecMulVec v v) * η i) / s
                  = (∑ i, tracePair (A i) (Matrix.vecMulVec v v) * η i +
                      tracePair C (Matrix.vecMulVec v v) * s) / s := by
                field_simp; ring
              rw [this]; exact div_nonneg hv hspos.le
            · have e3 : ∑ i, b i * y i = -(∑ i, b i * η i) / s := by
                rw [← hsum b]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
              rw [e3, lt_div_iff₀ hspos]
              nlinarith
          have PS : PrimalStrict A b → (∃ y, DualFeasible A C y) →
              ∃ y, DualFeasible A C y ∧ (∀ w, DualFeasible A C w → ∑ i, b i * w i ≤ ∑ i, b i * y i) ∧
                ∀ δ > 0, ∃ X, PrimalFeasible A b X ∧ tracePair C X < ∑ i, b i * y i + δ := by
            rintro ⟨X0, hX0, hX0b⟩ ⟨y1, hy1⟩
            obtain ⟨lam, hlam, hL⟩ := Hlam X0 hX0
            let L : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) := Submodule.span ℝ (Set.range A)
            have hLc : IsClosed (L : Set (Matrix (Fin n) (Fin n) ℝ)) := L.closed_of_finiteDimensional
            have hLb : ∀ W ∈ L, ∃ y : Fin m → ℝ, W = ∑ i, y i • A i := fun W hW => by
              obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hW; exact ⟨c, hc.symm⟩
            have hLs : ∀ y : Fin m → ℝ, ∑ i, y i • A i ∈ L := fun y =>
              Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
            have hX0A : ∀ i, tracePair X0 (A i) = b i := fun i => by
              rw [← hX0b i]; unfold tracePair; rw [Matrix.trace_mul_comm]
            have hX0y : ∀ y : Fin m → ℝ, tracePair X0 (∑ i, y i • A i) = ∑ i, b i * y i := by
              intro y; unfold tracePair
              rw [Matrix.mul_sum, Matrix.trace_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
              have := hX0A i; unfold tracePair at this; rw [this]; ring
            let h : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × ℝ → Matrix (Fin n) (Fin n) ℝ × ℝ :=
              fun p => (p.1 + p.2.1, tracePair X0 p.1 - p.2.2)
            let P : Set (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ × ℝ) :=
              {p | p.1 ∈ L ∧ p.2.1.PosSemidef ∧ 0 ≤ p.2.2}
            have hK : IsClosed (h '' P) := by
              refine closedImg P h (fun q => ‖q.1‖ + (2/lam + 1) * (tracePair X0 q.1 - q.2)) ?_ ?_ ?_ ?_
              · exact (hLc.preimage continuous_fst).inter ((HC.preimage (continuous_fst.comp continuous_snd)).inter
                  (isClosed_le continuous_const (continuous_snd.comp continuous_snd)))
              · refine Continuous.prodMk (continuous_fst.add (continuous_fst.comp continuous_snd)) ?_
                exact ((Hcont _).comp continuous_fst).sub (continuous_snd.comp continuous_snd)
              · exact continuous_norm.comp continuous_fst |>.add (continuous_const.mul
                  (((Hcont _).comp continuous_fst).sub continuous_snd))
              · rintro ⟨W, S, r⟩ ⟨hW, hS, hr⟩
                simp only at hW hS hr
                have e1 := H1 _ _ hL hS
                rw [Hlam'] at e1
                have hn := Hnorm S hS
                have hts := hS.trace_nonneg
                set a := tracePair X0 S
                have ha : 0 ≤ a := by nlinarith
                have htx : S.trace ≤ a / lam := by rw [le_div_iff₀ hlam]; linarith
                have hq : ‖W + S‖ + (2/lam + 1) * (tracePair X0 (W + S) - (tracePair X0 W - r))
                    = ‖W + S‖ + 2 * (a / lam) + a + 2 * (r / lam) + r := by
                  rw [HtpAdd]; simp only [a]; field_simp; ring
                show ‖(W, S, r)‖ ≤ ‖W + S‖ + (2/lam + 1) * (tracePair X0 (W + S) - (tracePair X0 W - r))
                rw [hq, norm_prod_le_iff, norm_prod_le_iff]
                have : 0 ≤ r / lam := div_nonneg hr hlam.le
                have : 0 ≤ a / lam := div_nonneg ha hlam.le
                have hWn : ‖W‖ ≤ ‖W + S‖ + ‖S‖ := by
                  have := norm_sub_le (W + S) S; simpa using this
                have := norm_nonneg (W + S)
                refine ⟨by dsimp only; linarith, by dsimp only; linarith, ?_⟩
                simp only [Real.norm_eq_abs, abs_of_nonneg hr]; linarith
            have hKconv : Convex ℝ (h '' P) := by
              rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ a c ha hc hac
              refine ⟨a • p + c • q, ⟨?_, ?_, ?_⟩, ?_⟩
              · exact L.add_mem (L.smul_mem a hp.1) (L.smul_mem c hq.1)
              · exact (hp.2.1.smul ha).add (hq.2.1.smul hc)
              · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; nlinarith [hp.2.2, hq.2.2]
              · refine Prod.ext ?_ ?_
                · simp only [h, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Prod.smul_mk,
                    Prod.mk_add_mk, smul_add]; abel
                · simp only [h, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, HtpAdd, HtpSmul,
                    Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]; ring
            let T : Set ℝ := {t | (C, t) ∈ h '' P}
            have hTc : IsClosed T := hK.preimage (by fun_prop)
            have hy1T : ∑ i, b i * y1 i ∈ T :=
              ⟨(∑ i, y1 i • A i, C - ∑ i, y1 i • A i, 0), ⟨hLs y1, hy1, le_refl _⟩, by
                simp only [h, add_sub_cancel, hX0y, sub_zero]⟩
            have hTb : BddAbove T := ⟨tracePair X0 C, by
              rintro t ⟨⟨W, S, r⟩, ⟨hW, hS, hr⟩, he⟩
              simp only [h, Prod.mk.injEq] at he hW hS hr
              have := H1 _ _ hX0.posSemidef hS
              rw [← he.1, HtpAdd]; linarith [he.2]⟩
            have htmem := hTc.csSup_mem ⟨_, hy1T⟩ hTb
            set ts := sSup T
            obtain ⟨⟨Ws, Ss, rs⟩, ⟨hWs, hSs, hrs⟩, hes⟩ := htmem
            simp only [h, Prod.mk.injEq] at hes hWs hSs hrs
            obtain ⟨ys, rfl⟩ := hLb _ hWs
            have hysF : DualFeasible A C ys := by
              have : C - ∑ i, ys i • A i = Ss := by rw [← hes.1]; abel
              unfold DualFeasible; rw [this]; exact hSs
            have hval : ts ≤ ∑ i, b i * ys i := by rw [← hX0y]; linarith [hes.2]
            have hmax : ∀ w, DualFeasible A C w → ∑ i, b i * w i ≤ ts := fun w hw =>
              le_csSup hTb ⟨(∑ i, w i • A i, C - ∑ i, w i • A i, 0), ⟨hLs w, hw, le_refl _⟩, by
                simp only [h, add_sub_cancel, hX0y, sub_zero]⟩
            refine ⟨ys, hysF, fun w hw => (hmax w hw).trans hval, fun δ hδ => ?_⟩
            have hnot : (C, ts + δ) ∉ h '' P := fun hin => by
              have := le_csSup hTb hin; linarith
            have : LocallyConvexSpace ℝ (Matrix (Fin n) (Fin n) ℝ × ℝ) := NormedSpace.toLocallyConvexSpace
            obtain ⟨f, u, hfu, hfK⟩ := geometric_hahn_banach_point_closed hKconv hK hnot
            set s := f (0, 1) with hs
            let G : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun j i => f (Matrix.single i j 1, 0)
            have hrep : ∀ (M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ), f (M, t) = tracePair G M + t * s := by
              intro M t
              have e1 : (M, t) = ((M, 0) : Matrix (Fin n) (Fin n) ℝ × ℝ) +
                  t • ((0 : Matrix (Fin n) (Fin n) ℝ), (1:ℝ)) := by simp
              have e2 : ((M, 0) : Matrix (Fin n) (Fin n) ℝ × ℝ) =
                  ∑ i, ∑ j, M i j • ((Matrix.single i j 1 : Matrix (Fin n) (Fin n) ℝ), (0:ℝ)) := by
                refine Prod.ext ?_ ?_
                · rw [Prod.fst_sum]; simp only [Prod.fst_sum, Prod.smul_fst]
                  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
                  simp [Matrix.smul_single]
                · simp [Prod.snd_sum]
              rw [e1, e2, map_add, map_sum, map_smul]
              simp only [map_sum, map_smul, smul_eq_mul]
              congr 1
              simp only [tracePair, Matrix.trace, Matrix.diag, Matrix.mul_apply, G, Matrix.of_apply]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring
            have h0K : ((0 : Matrix (Fin n) (Fin n) ℝ), (0:ℝ)) ∈ h '' P :=
              ⟨(0, 0, 0), ⟨L.zero_mem, Matrix.PosSemidef.zero, le_rfl⟩, by simp [h, tracePair]⟩
            have hu : u < 0 := by have := hfK _ h0K; rwa [Prod.mk_zero_zero, map_zero] at this
            have hnn : ∀ p ∈ P, 0 ≤ f (h p) := by
              intro p hp
              refine cone _ u hu fun a ha => ?_
              have hmem : h (a • p) ∈ h '' P := ⟨_, ⟨L.smul_mem a hp.1, hp.2.1.smul ha.le, by
                simp only [Prod.smul_snd, smul_eq_mul]; exact mul_nonneg ha.le hp.2.2⟩, rfl⟩
              have e : h (a • p) = a • h p := by
                ext
                · simp [h, smul_add]
                · simp [h, HtpSmul]; ring
              have := hfK _ hmem
              rwa [e, map_smul, smul_eq_mul] at this
            have hsle : s ≤ 0 := by
              have := hnn (0, 0, 1) ⟨L.zero_mem, Matrix.PosSemidef.zero, zero_le_one⟩
              simp [h, hrep, tracePair] at this; linarith
            have hAi : ∀ i, tracePair G (A i) = -(b i * s) := by
              intro i
              have h1 := hnn (A i, 0, 0) ⟨Submodule.subset_span ⟨i, rfl⟩, Matrix.PosSemidef.zero, le_rfl⟩
              have h2 := hnn (-A i, 0, 0) ⟨L.neg_mem (Submodule.subset_span ⟨i, rfl⟩),
                Matrix.PosSemidef.zero, le_rfl⟩
              simp only [h, add_zero, sub_zero, hrep, hX0A] at h1 h2
              have : tracePair X0 (-A i) = -b i := by
                rw [show -A i = (-1:ℝ) • A i by simp, HtpSmul, hX0A]; ring
              have h3 : tracePair G (-A i) = -tracePair G (A i) := by
                rw [show -A i = (-1:ℝ) • A i by simp, HtpSmul]; ring
              rw [this, h3] at h2
              linarith
            have hSn : ∀ S, S.PosSemidef → 0 ≤ tracePair G S := by
              intro S hS
              have := hnn (0, S, 0) ⟨L.zero_mem, hS, le_rfl⟩
              simpa [h, hrep, tracePair] using this
            have hk := hnn (∑ i, ys i • A i, Ss, rs) ⟨hWs, hSs, hrs⟩
            simp only [h, hrep] at hk
            rw [hes.1, hes.2] at hk
            rw [hrep] at hfu
            have hsneg : s < 0 := by
              rcases hsle.lt_or_eq with h' | h'
              · exact h'
              · rw [h'] at hk hfu; simp at hk hfu; linarith
            have hGT : ∀ M : Matrix (Fin n) (Fin n) ℝ, M.IsSymm → tracePair G.transpose M = tracePair G M := by
              intro M hM
              unfold tracePair
              rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose, hM.eq,
                Matrix.trace_mul_comm]
            let X : Matrix (Fin n) (Fin n) ℝ := (-1/s) • ((1/2 : ℝ) • (G + G.transpose))
            have hXM : ∀ M : Matrix (Fin n) (Fin n) ℝ, M.IsSymm → tracePair M X = (-1/s) * tracePair G M := by
              intro M hM
              have : tracePair M X = tracePair X M := by unfold tracePair; rw [Matrix.trace_mul_comm]
              rw [this]
              have e : tracePair X M = (-1/s) * ((1/2) * (tracePair G M + tracePair G.transpose M)) := by
                simp only [X, tracePair, Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul, Matrix.trace_add,
                  smul_eq_mul]
              rw [e, hGT M hM]; ring
            refine ⟨X, ⟨?_, fun i => ?_⟩, ?_⟩
            · refine H2 _ ?_ fun v => ?_
              · unfold Matrix.IsSymm
                simp only [X, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
              · have hvs : (Matrix.vecMulVec v v).IsSymm := by
                  unfold Matrix.IsSymm; ext i j; simp [Matrix.vecMulVec_apply, mul_comm]
                have := hXM _ hvs
                have hXv : tracePair X (Matrix.vecMulVec v v) = tracePair (Matrix.vecMulVec v v) X := by
                  unfold tracePair; rw [Matrix.trace_mul_comm]
                rw [hXv, this]
                exact mul_nonneg (div_pos_of_neg_of_neg (by norm_num) hsneg).le (hSn _ (HvvPSD v))
            · rw [hXM _ (hA i), hAi i]; field_simp; exact mul_div_cancel_left₀ _ hsneg.ne
            · rw [hXM _ hC]
              have : (-1/s) * tracePair G C < ts + δ := by
                rw [show (-1/s) * tracePair G C = tracePair G C / (-s) by field_simp]
                rw [div_lt_iff₀ (by linarith)]; nlinarith
              linarith
          refine ⟨?_, ?_⟩
          · rintro ⟨⟨X1, hX1⟩, ⟨y1, hy1⟩, hstrict⟩ ε hε
            rcases hstrict with hp | hd
            · obtain ⟨ys, hys, -, happ⟩ := PS hp ⟨y1, hy1⟩
              obtain ⟨X, hX, hlt⟩ := happ ε hε
              exact ⟨X, ys, hX, hys, by linarith⟩
            · obtain ⟨Xs, hXs, -, happ⟩ := DS hd ⟨X1, hX1⟩
              obtain ⟨y, hy, hlt⟩ := happ ε hε
              exact ⟨Xs, y, hXs, hy, by linarith⟩
          · rintro ⟨hp, hd⟩
            obtain ⟨X0, hX0, hX0b⟩ := hp
            obtain ⟨y0, hy0⟩ := hd
            obtain ⟨Xs, hXs, hXmin, happ⟩ := DS ⟨y0, hy0⟩ ⟨X0, hX0.posSemidef, hX0b⟩
            obtain ⟨ys, hys, hymax, -⟩ := PS ⟨X0, hX0, hX0b⟩ ⟨y0, hy0.posSemidef⟩
            refine ⟨Xs, ys, hXs, hys, le_antisymm ?_ (weak Xs ys hXs hys), hXmin, hymax⟩
            refine le_of_forall_pos_lt_add fun δ hδ => ?_
            obtain ⟨y, hy, hlt⟩ := happ δ hδ
            linarith [hymax y hy]
