-- Prove2me | solution 1 for RiskAverseSDDP.Convergence.eq_4_26
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:15:49.75134+00:00
-- url     : https://prove2.me/submissions/60c9e616-21cc-4a90-9bc9-32d29a75b839
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run
import Theorems.Thm_RiskAverseSDDP_Convergence_proposition_3_1
import Theorems.Thm_RiskAverseSDDP_Convergence_lemma_3_4

open RiskAverseSDDP.Convergence

namespace RASDDPEq426

lemma mul_add_coe {w : ℝ} (hw : 0 ≤ w) (z : EReal) (c : ℝ) :
    (w : EReal) * (z + (c : EReal)) = (w : EReal) * z + ((w * c : ℝ) : EReal) := by
  rw [EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hw) (EReal.coe_ne_top w),
    EReal.coe_mul]

lemma sum_add_coe {M : ℕ} (a : Fin M → EReal) (b : Fin M → ℝ) :
    ∑ j, (a j + ((b j : ℝ) : EReal)) = (∑ j, a j) + ((∑ j, b j : ℝ) : EReal) := by
  rw [Finset.sum_add_distrib]
  congr 1
  induction (Finset.univ : Finset (Fin M)) using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, EReal.coe_add]

lemma stageVal_mono {T n M q p : ℕ} (D : Model T n M q p) (s : ℕ) (j : Fin M)
    {V W : Hist n (s + 1) → EReal} (h : ∀ y, V y ≤ W y) (x : Hist n s) :
    D.stageVal s j V x ≤ D.stageVal s j W x := by
  unfold Model.stageVal
  exact iInf₂_mono fun y _ => add_le_add_right (h _) _

lemma Q_last {T n M q p : ℕ} (D : Model T n M q p) (x : Hist n T) : D.Q T x = 0 := by
  simp [Model.Q, Model.Qaux]

lemma Q_succ {T n M q p : ℕ} (D : Model T n M q p) (s : ℕ) (hs : s + 2 ≤ T)
    (x : Hist n (s + 1)) :
    D.Q (s + 1) x = D.rho (s + 2) (fun j => D.stageVal (s + 1) j (D.Q (s + 2)) x) := by
  have h : T - (s + 1) = (T - (s + 2)) + 1 := by omega
  rw [Model.Q, h, Model.Qaux]
  rfl

/-- Validity of the cuts (Lemma 3.2(a), everywhere): `𝒬^k_h ≤ 𝒬_h`. -/
lemma valid {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (hS : D.Standing) (R : Rules n M)
    (ys : ℕ → ℕ → Fin M) (r : RunData n M) (hr : D.IsRun R ys r) :
    ∀ d h, h + d = T → 1 ≤ h → ∀ k y, r.Qm k h y ≤ D.Q h y := by
  obtain ⟨hQ0, hQT, _, hcut⟩ := hr
  intro d
  induction d with
  | zero =>
    intro h hh _ k y
    have hh' : h = T := by omega
    subst hh'
    rw [hQT k, Q_last]
  | succ d ih =>
    intro h hh h1 k y
    obtain ⟨s, rfl⟩ : ∃ s, h = s + 1 := ⟨h - 1, by omega⟩
    have hs : s + 2 ≤ T := by omega
    have ih' := ih (s + 2) (by omega) (by omega)
    induction k generalizing y with
    | zero => rw [hQ0 (s + 1) h1 (by omega)]; exact bot_le
    | succ k ihk =>
      obtain ⟨hpk, _, hπ, hθ, hβ, hupd⟩ := hcut k s hs
      rw [hupd]
      refine max_le (ihk y) ?_
      set xt := r.hist (k + 1) s (sampNode ys (k + 1) s)
      set Z : Fin M → EReal := fun j => D.stageVal (s + 1) j (r.Qm k (s + 2)) xt
      set pk := R.pRule (s + 2) Z
      set d' := y - xt
      have hw : ∀ j, 0 ≤ pk j * D.Φ (s + 2) j := by
        intro j
        have hS' := hS (s + 2) (by omega) hs
        exact mul_nonneg ((hS'.2.2.1 hpk).1 j) (hS'.1 j).le
      have hinner : inner ℝ (r.β (k + 1) s) d' =
          ∑ j, (pk j * D.Φ (s + 2) j) * inner ℝ (r.π (k + 1) s j) d' := by
        rw [hβ, sum_inner]
        simp only [real_inner_smul_left]
      have hsub : ∀ j, Z j + ((inner ℝ (r.π (k + 1) s j) d' : ℝ) : EReal) ≤
          D.stageVal (s + 1) j (D.Q (s + 2)) y := by
        intro j
        exact ((hπ j).2 y).trans (stageVal_mono D (s + 1) j (ih' k) _)
      calc r.θ (k + 1) s + ((inner ℝ (r.β (k + 1) s) d' : ℝ) : EReal)
          = ∑ j, (((pk j * D.Φ (s + 2) j : ℝ) : EReal) * Z j +
              (((pk j * D.Φ (s + 2) j) * inner ℝ (r.π (k + 1) s j) d' : ℝ) : EReal)) := by
            rw [sum_add_coe, hθ, hinner]; rfl
        _ = ∑ j, ((pk j * D.Φ (s + 2) j : ℝ) : EReal) *
              (Z j + ((inner ℝ (r.π (k + 1) s j) d' : ℝ) : EReal)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [mul_add_coe (hw j)]
        _ ≤ ∑ j, ((pk j * D.Φ (s + 2) j : ℝ) : EReal) * D.stageVal (s + 1) j (D.Q (s + 2)) y := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact mul_le_mul_of_nonneg_left (hsub j) (by exact_mod_cast hw j)
        _ = D.wsum (s + 2) pk (fun j => D.stageVal (s + 1) j (D.Q (s + 2)) y) := rfl
        _ ≤ D.rho (s + 2) (fun j => D.stageVal (s + 1) j (D.Q (s + 2)) y) := by
            unfold Model.rho
            exact le_iSup₂ (f := fun π _ => D.wsum (s + 2) π
              (fun j => D.stageVal (s + 1) j (D.Q (s + 2)) y)) pk hpk
        _ = D.Q (s + 1) y := (Q_succ D s hs y).symm

lemma snoc_mem_prodSet {T n M q p s : ℕ} (D : Model T n M q p) {x : Hist n s}
    {y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ D.prodSet s) (hy : y ∈ D.Xc (s + 1)) :
    x.snoc y ∈ D.prodSet (s + 1) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Hist.snoc, PiLp.toLp_apply, Fin.snoc_last, Fin.val_last]; exact hy
  · simp only [Hist.snoc, PiLp.toLp_apply, Fin.snoc_castSucc, Fin.coe_castSucc]; exact hx j

lemma hist_mem {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (R : Rules n M)
    (ys : ℕ → ℕ → Fin M) (r : RunData n M) (hr : D.IsRun R ys r) (k : ℕ) :
    ∀ s, s < T → ∀ ν : Fin s → Fin M, r.hist (k + 1) s ν ∈ D.prodSet (s + 1) := by
  intro s
  induction s with
  | zero =>
    intro hs ν
    have h := (hr.2.2.1 k 0 ν hs).2.1
    exact snoc_mem_prodSet D (fun i => Fin.elim0 i) h.1
  | succ s ih =>
    intro hs ν
    have h := (hr.2.2.1 k (s + 1) ν hs).2.1
    exact snoc_mem_prodSet D (ih (by omega) (Fin.init ν)) h.1

lemma sum_ne_bot {M : ℕ} (a : Fin M → EReal) (h : ∀ j, a j ≠ ⊥) : ∑ j, a j ≠ ⊥ := by
  induction (Finset.univ : Finset (Fin M)) using Finset.induction_on with
  | empty => simp
  | insert b t hb ih =>
    rw [Finset.sum_insert hb]
    exact EReal.add_ne_bot_iff.2 ⟨h b, ih⟩

lemma coe_mul_ne_bot {w : ℝ} (hw : 0 ≤ w) {z : EReal} (hz : z ≠ ⊥) : (w : EReal) * z ≠ ⊥ := by
  induction z using EReal.rec with
  | bot => exact absurd rfl hz
  | top =>
    rcases hw.eq_or_lt with h | h
    · subst h; simp
    · rw [EReal.coe_mul_top_of_pos h]; exact top_ne_bot
  | coe c => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _

/-- A nonnegative weighted sum with one term `w_j * ⊤`, `w_j > 0`, is `⊤`. -/
lemma sum_eq_top {M : ℕ} (w : Fin M → ℝ) (G : Fin M → EReal) (hw : ∀ j, 0 ≤ w j)
    (hG : ∀ j, 0 ≤ G j) (j : Fin M) (hj : 0 < w j) (hGj : G j = ⊤) :
    ∑ i, (w i : EReal) * G i = ⊤ := by
  refine top_le_iff.1 ?_
  have : (w j : EReal) * G j ≤ ∑ i, (w i : EReal) * G i :=
    Finset.single_le_sum (f := fun i => (w i : EReal) * G i)
      (fun i _ => mul_nonneg (by exact_mod_cast hw i) (hG i)) (Finset.mem_univ j)
  rw [hGj, EReal.coe_mul_top_of_pos hj] at this
  exact this

end RASDDPEq426

open RASDDPEq426 in
theorem solution {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) (ys : ℕ → ℕ → Fin M) (r : RunData n M)
    (hr : D.IsRun R ys r) :
    ∀ s, s + 2 ≤ T → ∀ (ν : Fin s → Fin M) (k : ℕ), sampNode ys (k + 1) s = ν →
      0 ≤ D.Q (s + 1) (r.hist (k + 1) s ν) - r.Qm (k + 1) (s + 1) (r.hist (k + 1) s ν) ∧
      D.Q (s + 1) (r.hist (k + 1) s ν) - r.Qm (k + 1) (s + 1) (r.hist (k + 1) s ν) ≤
        D.rho (s + 2) (fun j =>
          D.Q (s + 2) (r.hist (k + 1) (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j)) -
            r.Qm k (s + 2) (r.hist (k + 1) (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j))) := by
  intro s hs ν k hsamp
  have hε : 0 < ε := hH2.1
  set X := r.hist (k + 1) s ν with hXdef
  have hX : X ∈ D.prodSet (s + 1) := hist_mem D R ys r hr k s (by omega) ν
  have hQX : D.Q (s + 1) X ≠ ⊥ ∧ D.Q (s + 1) X ≠ ⊤ :=
    (proposition_3_1 D ε hS hH2 (s + 1) (by omega) (by omega) (ε / 2) (by linarith)
      (by linarith)).2.1 X (Metric.self_subset_cthickening _ hX)
  have hval1 := valid D hS R ys r hr (T - (s + 1)) (s + 1) (by omega) (by omega)
  have hval2 := valid D hS R ys r hr (T - (s + 2)) (s + 2) (by omega) (by omega)
  -- children of the node
  set ch : Fin M → Hist n (s + 2) := fun j =>
    r.hist (k + 1) (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j) with hch
  set xc : Fin M → EuclideanSpace ℝ (Fin n) := fun j =>
    r.x (k + 1) (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j)
  have hchX : ∀ j, ch j = X.snoc (xc j) := by
    intro j
    simp only [hch, RunData.hist, Fin.init_snoc, hXdef]
    rfl
  have hfw : ∀ j, xc j ∈ D.feas (s + 1) j X ∧ ∀ y ∈ D.feas (s + 1) j X,
      D.f (s + 2) j (X.snoc (xc j)) + r.Qm k (s + 2) (X.snoc (xc j)) ≤
        D.f (s + 2) j (X.snoc y) + r.Qm k (s + 2) (X.snoc y) := by
    intro j
    obtain ⟨_, h1, h2⟩ := hr.2.2.1 k (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j) (by omega)
    have hp : r.phist (k + 1) (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j) = X := by
      simp only [RunData.phist, Fin.init_snoc, hXdef]
    have hn : nodeRlz (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j) = j := by
      simp [nodeRlz]
    rw [hp, hn] at h1 h2
    exact ⟨h1, h2⟩
  have hchP : ∀ j, ch j ∈ D.prodSet (s + 2) := fun j =>
    hist_mem D R ys r hr k (s + 1) (by omega) _
  have hQc : ∀ j, D.Q (s + 2) (ch j) ≠ ⊥ ∧ D.Q (s + 2) (ch j) ≠ ⊤ := fun j =>
    (proposition_3_1 D ε hS hH2 (s + 2) (by omega) hs (ε / 2) (by linarith)
      (by linarith)).2.1 _ (Metric.self_subset_cthickening _ (hchP j))
  obtain ⟨-, -, -, hdom, -, -⟩ := hH2.2 (s + 1) (by omega)
  have hfc : ∀ j, D.f (s + 2) j (ch j) ≠ ⊥ ∧ D.f (s + 2) j (ch j) ≠ ⊤ := by
    intro j
    obtain ⟨-, hf, -⟩ := hH2.2 (s + 1) (by omega)
    have hj : j ∈ Model.Rlz (M := M) (s + 1 + 1) := by simp [Model.Rlz]
    refine ⟨(hf j hj).1.1 _, ?_⟩
    rw [hchX j]
    exact (hdom j hj X (Metric.self_subset_cthickening _ hX) (xc j) (hfw j).1.1).ne
  -- the cut at the sampled node
  subst hsamp
  have h34 := lemma_3_4 D ε hS hH2 R ys r hr s hs (k + 1) (by omega)
  obtain ⟨hpk, hrk, -, hθ, -, -⟩ := hr.2.2.2 k s hs
  set Z : Fin M → EReal := fun j => D.stageVal (s + 1) j (r.Qm k (s + 2)) X with hZ
  set A : Fin M → EReal := fun j => D.stageVal (s + 1) j (D.Q (s + 2)) X with hA
  set G : Fin M → EReal := fun j => D.Q (s + 2) (ch j) - r.Qm k (s + 2) (ch j) with hG
  have hQm : r.Qm (k + 1) (s + 1) X = D.rho (s + 2) Z := by
    rw [h34, hθ]; exact hrk
  have hQXA : D.Q (s + 1) X = D.rho (s + 2) A := Q_succ D s hs X
  have hZc : ∀ j, Z j = D.f (s + 2) j (ch j) + r.Qm k (s + 2) (ch j) := by
    intro j
    rw [hchX j]
    apply le_antisymm
    · exact iInf₂_le (f := fun y _ => D.f (s + 1 + 1) j (X.snoc y) +
        r.Qm k (s + 1 + 1) (X.snoc y)) (xc j) (hfw j).1
    · exact le_iInf₂ fun y hy => (hfw j).2 y hy
  have hAc : ∀ j, A j ≤ D.f (s + 2) j (ch j) + D.Q (s + 2) (ch j) := by
    intro j
    rw [hchX j]
    exact iInf₂_le (f := fun y _ => D.f (s + 1 + 1) j (X.snoc y) +
        D.Q (s + 1 + 1) (X.snoc y)) (xc j) (hfw j).1
  have hGnn : ∀ j, 0 ≤ G j := fun j =>
    (EReal.sub_nonneg (Or.inl (hQc j).2) (Or.inl (hQc j).1)).2 (hval2 k _)
  have hwp : ∀ π ∈ D.Prisk (s + 2), ∀ j, 0 ≤ π j * D.Φ (s + 2) j := by
    intro π hπ j
    have hS' := hS (s + 2) (by omega) hs
    exact mul_nonneg ((hS'.2.2.1 hπ).1 j) (hS'.1 j).le
  -- if some positive weight sits on a child where 𝒬^k = -∞, the right side is +∞
  have htop : ∀ π ∈ D.Prisk (s + 2), ∀ j, 0 < π j * D.Φ (s + 2) j →
      r.Qm k (s + 2) (ch j) = ⊥ → D.rho (s + 2) G = ⊤ := by
    intro π hπ j hwj hmj
    refine top_le_iff.1 ?_
    have hGj : G j = ⊤ := by simp only [hG, hmj]; exact EReal.sub_bot (hQc j).1
    have hs1 : D.wsum (s + 2) π G = ⊤ :=
      sum_eq_top (fun i => π i * D.Φ (s + 2) i) G (hwp π hπ) hGnn j hwj hGj
    rw [← hs1]
    unfold Model.rho
    exact le_iSup₂ (f := fun π _ => D.wsum (s + 2) π G) π hπ
  refine ⟨?_, ?_⟩
  · exact (EReal.sub_nonneg (Or.inl hQX.2) (Or.inl hQX.1)).2 (hval1 (k + 1) X)
  · rw [hQm]
    by_cases hZb : D.rho (s + 2) Z = ⊥
    · -- the approximation is -∞ at the trial point
      rw [hZb, EReal.sub_bot hQX.1]
      have hws : D.wsum (s + 2) (R.pRule (s + 2) Z) Z = ⊥ := by rw [hrk]; exact hZb
      by_contra hne
      apply sum_ne_bot _ _ hws
      intro j hj
      have hw := hwp _ hpk j
      rcases hw.eq_or_lt with h0 | hpos
      · rw [← h0] at hj; simp at hj
      · have hZj : Z j = ⊥ := by
          by_contra hzj; exact coe_mul_ne_bot hw hzj hj
        have hmj : r.Qm k (s + 2) (ch j) = ⊥ := by
          rw [hZc j] at hZj
          rcases EReal.add_eq_bot_iff.1 hZj with h | h
          · exact absurd h (hfc j).1
          · exact h
        exact hne (by rw [htop _ hpk j hpos hmj])
    · have hZt : D.rho (s + 2) Z ≠ ⊤ := by
        rw [← hQm]; exact ne_top_of_le_ne_top hQX.2 (hval1 (k + 1) X)
      rw [EReal.sub_le_iff_le_add (Or.inl hZb) (Or.inl hZt), hQXA]
      unfold Model.rho
      refine iSup₂_le fun π hπ => ?_
      by_cases hbad : ∃ j, 0 < π j * D.Φ (s + 2) j ∧ r.Qm k (s + 2) (ch j) = ⊥
      · obtain ⟨j, hwj, hmj⟩ := hbad
        have := htop π hπ j hwj hmj
        unfold Model.rho at this
        rw [this, EReal.top_add_of_ne_bot
          (show (⨆ π ∈ D.Prisk (s + 2), D.wsum (s + 2) π Z) ≠ ⊥ from hZb)]
        exact le_top
      · push_neg at hbad
        have hterm : ∀ j, ((π j * D.Φ (s + 2) j : ℝ) : EReal) * A j ≤
            ((π j * D.Φ (s + 2) j : ℝ) : EReal) * G j +
              ((π j * D.Φ (s + 2) j : ℝ) : EReal) * Z j := by
          intro j
          have hw := hwp π hπ j
          rcases hw.eq_or_lt with h0 | hpos
          · rw [← h0]; simp
          · have hmb := hbad j hpos
            have hmt : r.Qm k (s + 2) (ch j) ≠ ⊤ :=
              ne_top_of_le_ne_top (hQc j).2 (hval2 k _)
            rw [← EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast hw)
              (EReal.coe_ne_top _)]
            refine mul_le_mul_of_nonneg_left ((hAc j).trans (le_of_eq ?_))
              (by exact_mod_cast hw)
            rw [hZc j]
            simp only [hG]
            lift D.f (s + 2) j (ch j) to ℝ using ⟨(hfc j).2, (hfc j).1⟩ with fv
            lift D.Q (s + 2) (ch j) to ℝ using ⟨(hQc j).2, (hQc j).1⟩ with qv
            lift r.Qm k (s + 2) (ch j) to ℝ using ⟨hmt, hmb⟩ with mv
            rw [← EReal.coe_sub, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add]
            congr 1; ring
        calc D.wsum (s + 2) π A
            ≤ ∑ j, (((π j * D.Φ (s + 2) j : ℝ) : EReal) * G j +
                ((π j * D.Φ (s + 2) j : ℝ) : EReal) * Z j) :=
              Finset.sum_le_sum fun j _ => hterm j
          _ = D.wsum (s + 2) π G + D.wsum (s + 2) π Z := Finset.sum_add_distrib
          _ ≤ (⨆ π ∈ D.Prisk (s + 2), D.wsum (s + 2) π G) + D.rho (s + 2) Z := by
              refine add_le_add ?_ ?_
              · exact le_iSup₂ (f := fun π _ => D.wsum (s + 2) π G) π hπ
              · unfold Model.rho
                exact le_iSup₂ (f := fun π _ => D.wsum (s + 2) π Z) π hπ
