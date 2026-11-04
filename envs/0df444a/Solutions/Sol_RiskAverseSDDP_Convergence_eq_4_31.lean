-- Prove2me | solution 1 for RiskAverseSDDP.Convergence.eq_4_31
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:12:12.025536+00:00
-- url     : https://prove2.me/submissions/3bb447d7-c979-454d-8d8d-2a0bc5c16cf6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run
import Theorems.Thm_RiskAverseSDDP_Convergence_proposition_3_1

open RiskAverseSDDP.Convergence

namespace RASDDPEq431

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

lemma snoc_continuous {n s : ℕ} (x : Hist n s) : Continuous (fun y => x.snoc y) := by
  unfold Hist.snoc
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]; exact continuous_id
  · simp only [Fin.snoc_castSucc]; exact continuous_const

lemma snoc_mem_prodSet {T n M q p : ℕ} (D : Model T n M q p) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ D.Xc 1) : (Hist.empty n).snoc y ∈ D.prodSet 1 := by
  intro i
  have hi : i = Fin.last 0 := Subsingleton.elim _ _
  subst hi
  show (WithLp.toLp 2 _ : Hist n 1) (Fin.last 0) ∈ D.Xc ((Fin.last 0).val + 1)
  rw [PiLp.toLp_apply, Fin.snoc_last]
  simpa using hy

lemma final {a b f qm qq : EReal} (hb1 : b ≠ ⊥) (hb2 : b ≠ ⊤) (hf1 : f ≠ ⊥) (hf2 : f ≠ ⊤)
    (hq : qq ≠ ⊥) (ha : a = f + qm) (hbq : b ≤ f + qq) (hab : a ≤ b) (hqq : qm ≤ qq) :
    0 ≤ b - a ∧ b - a ≤ qq - qm := by
  lift b to ℝ using ⟨hb2, hb1⟩
  lift f to ℝ using ⟨hf2, hf1⟩
  subst ha
  induction qm using EReal.rec with
  | bot =>
    simp only [EReal.add_bot, EReal.sub_bot (EReal.coe_ne_bot b), EReal.sub_bot hq]
    exact ⟨le_top, le_rfl⟩
  | top =>
    exfalso
    rw [EReal.coe_add_top] at hab
    exact absurd hab (not_le.2 (EReal.coe_lt_top b))
  | coe m =>
    induction qq using EReal.rec with
    | bot => exact absurd rfl hq
    | top =>
      refine ⟨?_, ?_⟩
      · rw [← EReal.coe_add] at hab ⊢
        rw [← EReal.coe_sub]
        exact_mod_cast sub_nonneg.2 (by exact_mod_cast hab)
      · rw [EReal.top_sub_coe]; exact le_top
    | coe Qv =>
      rw [← EReal.coe_add] at hab hbq ⊢
      rw [← EReal.coe_sub, ← EReal.coe_sub]
      have hab' : f + m ≤ b := by exact_mod_cast hab
      have hbq' : b ≤ f + Qv := by exact_mod_cast hbq
      constructor
      · exact_mod_cast sub_nonneg.2 hab'
      · exact_mod_cast (by linarith : b - (f + m) ≤ Qv - m)

end RASDDPEq431

open RASDDPEq431 in
theorem solution {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ) (hT : 1 ≤ T)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) (ys : ℕ → ℕ → Fin M) (r : RunData n M)
    (hr : D.IsRun R ys r) :
    ∀ k : ℕ,
      0 ≤ D.Q1 - D.stageVal 0 0 (r.Qm k 1) (Hist.empty n) ∧
      D.Q1 - D.stageVal 0 0 (r.Qm k 1) (Hist.empty n) ≤
        D.Q 1 (r.hist (k + 1) 0 Fin.elim0) - r.Qm k 1 (r.hist (k + 1) 0 Fin.elim0) := by
  intro k
  have hε : 0 < ε := hH2.1
  obtain ⟨hX, hf, _, hdom, hne, _⟩ := hH2.2 0 hT
  have h0 : (0 : Fin M) ∈ Model.Rlz (M := M) (0 + 1) := by simp [Model.Rlz]
  obtain ⟨hprop, _, hlsc⟩ := hf 0 h0
  obtain ⟨_, hfin, hcont⟩ := proposition_3_1 D ε hS hH2 1 le_rfl hT (ε / 2) (by linarith)
    (by linarith)
  set e := Hist.empty n
  have hval := valid D hS R ys r hr (T - 1) 1 (by omega) le_rfl k
  -- the forward pass at the first-stage node
  obtain ⟨_, hxfeas, hxmin⟩ := hr.2.2.1 k 0 Fin.elim0 hT
  set x1 := r.x (k + 1) 0 Fin.elim0
  have hphist : r.phist (k + 1) 0 Fin.elim0 = e := rfl
  have hnr : nodeRlz 0 (Fin.elim0 : Fin 0 → Fin M) = 0 := rfl
  rw [hphist, hnr] at hxfeas hxmin
  have hhist : r.hist (k + 1) 0 Fin.elim0 = e.snoc x1 := rfl
  rw [hhist]
  have hx1X : x1 ∈ D.Xc 1 := hxfeas.1
  have hQfin : ∀ y ∈ D.Xc 1, D.Q 1 (e.snoc y) ≠ ⊥ ∧ D.Q 1 (e.snoc y) ≠ ⊤ := fun y hy =>
    hfin _ (Metric.self_subset_cthickening _ (snoc_mem_prodSet D y hy))
  have he : e ∈ Metric.cthickening ε (D.prodSet 0) :=
    Metric.self_subset_cthickening _ (fun i => Fin.elim0 i)
  have hf1 : D.f 1 0 (e.snoc x1) ≠ ⊥ := hprop.1 _
  have hf2 : D.f 1 0 (e.snoc x1) ≠ ⊤ := (hdom 0 h0 e he x1 hx1X).ne
  -- the approximate first-stage value is attained at x1
  have ha : D.stageVal 0 0 (r.Qm k 1) e = D.f 1 0 (e.snoc x1) + r.Qm k 1 (e.snoc x1) := by
    apply le_antisymm
    · exact iInf₂_le (f := fun y _ => D.f (0 + 1) 0 (e.snoc y) + r.Qm k (0 + 1) (e.snoc y))
        x1 hxfeas
    · exact le_iInf₂ fun y hy => hxmin y hy
  have hQ1 : D.Q1 = D.stageVal 0 0 (D.Q 1) e := rfl
  have hbq : D.Q1 ≤ D.f 1 0 (e.snoc x1) + D.Q 1 (e.snoc x1) := by
    rw [hQ1]
    exact iInf₂_le (f := fun y _ => D.f (0 + 1) 0 (e.snoc y) + D.Q (0 + 1) (e.snoc y)) x1 hxfeas
  have hab : D.stageVal 0 0 (r.Qm k 1) e ≤ D.Q1 := by
    rw [hQ1]; exact stageVal_mono D 0 0 (fun y => hval y) e
  -- finiteness of Q1
  have hb2 : D.Q1 ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hbq
    lift D.f 1 0 (e.snoc x1) to ℝ using ⟨hf2, hf1⟩ with fv
    lift D.Q 1 (e.snoc x1) to ℝ using ⟨(hQfin x1 hx1X).2, (hQfin x1 hx1X).1⟩ with qv
    exact (EReal.coe_add fv qv ▸ EReal.coe_ne_top _)
  have hb1 : D.Q1 ≠ ⊥ := by
    -- lower bounds for f and Q on the compact set 𝒳_1
    have hlsc' : LowerSemicontinuousOn (fun y => D.f 1 0 (e.snoc y)) (D.Xc 1) :=
      (hlsc.comp (snoc_continuous e)).lowerSemicontinuousOn _
    obtain ⟨y0, _, hy0⟩ := hlsc'.exists_isMinOn hX.1 hX.2.2
    have hcont' : ContinuousOn (fun y => (D.Q 1 (e.snoc y)).toReal) (D.Xc 1) :=
      hcont.comp (snoc_continuous e).continuousOn
        (fun y hy => Metric.self_subset_cthickening _ (snoc_mem_prodSet D y hy))
    obtain ⟨y1, _, hy1⟩ := hX.2.2.exists_isMinOn hX.1 hcont'
    have hf0 : D.f 1 0 (e.snoc y0) ≠ ⊥ := hprop.1 _
    have hlow : ((D.f 1 0 (e.snoc y0)).toReal + (D.Q 1 (e.snoc y1)).toReal : EReal) ≤ D.Q1 := by
      rw [hQ1]
      refine le_iInf₂ fun y hy => ?_
      have hyX : y ∈ D.Xc 1 := hy.1
      have h1 : D.f 1 0 (e.snoc y0) ≤ D.f 1 0 (e.snoc y) := hy0 hyX
      have h2 : (D.Q 1 (e.snoc y1)).toReal ≤ (D.Q 1 (e.snoc y)).toReal := hy1 hyX
      have hfy2 : D.f 1 0 (e.snoc y) ≠ ⊤ := (hdom 0 h0 e he y hyX).ne
      have hf0t : D.f 1 0 (e.snoc y0) ≠ ⊤ := ne_top_of_le_ne_top hfy2 h1
      have hQy := hQfin y hyX
      have e1 : ((D.f 1 0 (e.snoc y0)).toReal : EReal) = D.f 1 0 (e.snoc y0) :=
        EReal.coe_toReal hf0t hf0
      have e2 : ((D.Q 1 (e.snoc y)).toReal : EReal) = D.Q 1 (e.snoc y) :=
        EReal.coe_toReal hQy.2 hQy.1
      show _ ≤ D.f (0 + 1) 0 (e.snoc y) + D.Q (0 + 1) (e.snoc y)
      refine add_le_add (by rw [e1]; exact h1) ?_
      rw [← e2]; exact_mod_cast h2
    exact ne_bot_of_le_ne_bot (by rw [← EReal.coe_add]; exact EReal.coe_ne_bot _) hlow
  exact final hb1 hb2 hf1 hf2 (hQfin x1 hx1X).1 ha hbq hab (hval _)
