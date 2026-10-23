-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P18.classicalCommunicationBound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:57:19.273285+00:00
-- url     : https://prove2.me/submissions/7e9e2412-d380-4508-9c22-60a6c71902f8

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder
open Matrix

local notation "Γ" => QAlgorithms.Papers.Independent.Information100.P04.gamma

variable {A B C E : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E]

theorem x8_bound_aux {α : Type} [Fintype α] [DecidableEq α] (W : Matrix α α ℂ) (hW : W * Wᴴ = 1)
    (d : α → ℝ) (c : ℝ) (hc : ∀ k, |d k| ≤ c) :
    ((c : ℂ) • (1 : Matrix α α ℂ) + W * diagonal (fun k => (d k : ℂ)) * Wᴴ).PosSemidef ∧
    ((c : ℂ) • (1 : Matrix α α ℂ) - W * diagonal (fun k => (d k : ℂ)) * Wᴴ).PosSemidef := by
  have h1 : (c : ℂ) • (1 : Matrix α α ℂ) = W * diagonal (fun _ => (c : ℂ)) * Wᴴ := by
    rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hW]
  rw [h1, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add, ← Matrix.sub_mul, ← Matrix.mul_sub,
    diagonal_sub]
  constructor
  · refine PosSemidef.mul_mul_conjTranspose_same ?_ W
    rw [posSemidef_diagonal_iff]
    intro k
    have := (abs_le.1 (hc k)).1
    rw [← Complex.ofReal_add]
    exact Complex.zero_le_real.2 (by linarith)
  · refine PosSemidef.mul_mul_conjTranspose_same ?_ W
    rw [posSemidef_diagonal_iff]
    intro k
    have := (abs_le.1 (hc k)).2
    rw [← Complex.ofReal_sub]
    exact Complex.zero_le_real.2 (by linarith)

theorem x8_bound {α : Type} [Fintype α] [DecidableEq α] (H : Matrix α α ℂ) (hH : H.IsHermitian) :
    ∃ c : ℝ, 0 ≤ c ∧ ((c : ℂ) • (1 : Matrix α α ℂ) + H).PosSemidef ∧
      ((c : ℂ) • (1 : Matrix α α ℂ) - H).PosSemidef := by
  have hs : H = (hH.eigenvectorUnitary : Matrix α α ℂ) *
      diagonal (fun k => ((hH.eigenvalues k : ℝ) : ℂ)) * (hH.eigenvectorUnitary : Matrix α α ℂ)ᴴ := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  refine ⟨∑ k, |hH.eigenvalues k|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  have key := x8_bound_aux _ (Unitary.coe_mul_star_self hH.eigenvectorUnitary) _ _ fun k =>
    Finset.single_le_sum (f := fun k => |hH.eigenvalues k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
  rw [← hs] at key
  exact key

/-- the real value set of the correlation gauge -/
def x8G (s : Matrix (A × B) (A × B) ℂ) : Set ℝ :=
  {r | ∃ k l v, GammaFeasible s k l v ∧ r = (Matrix.kronecker k l).trace.re}

theorem x8_gamma_herm (s : Matrix (A × B) (A × B) ℂ) (hs : s.IsHermitian) : (Γ s).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, QAlgorithms.Papers.Independent.Information100.P04.gamma]
  exact hs.apply _ _

theorem x8_gamma_one (c : ℂ) : Γ (c • (1 : Matrix (A × B) (A × B) ℂ)) = c • 1 := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  simp only [QAlgorithms.Papers.Independent.Information100.P04.gamma, Matrix.smul_apply, Matrix.one_apply,
    Prod.mk.injEq]
  by_cases h1 : a = a' <;> by_cases h2 : b = b' <;> simp [h1, h2, eq_comm]

theorem x8_G_ne (s : Matrix (A × B) (A × B) ℂ) (hs : s.IsHermitian) : (x8G s).Nonempty := by
  obtain ⟨c, hc, h1, h2⟩ := x8_bound (Γ s) (x8_gamma_herm s hs)
  have hk : (Matrix.kronecker ((c : ℂ) • (1 : Matrix A A ℂ)) (1 : Matrix B B ℂ)) =
      (c : ℂ) • (1 : Matrix (A × B) (A × B) ℂ) := by
    simp only [Matrix.kronecker]
    rw [smul_kronecker, one_kronecker_one]
  have hH : ((c : ℂ) • (1 : Matrix A A ℂ)).IsHermitian := by
    simp [IsHermitian, conjTranspose_smul]
  have hH' : ((c : ℂ) • (1 : Matrix (A × B) (A × B) ℂ)).IsHermitian := by
    simp [IsHermitian, conjTranspose_smul]
  refine ⟨_, (c : ℂ) • (1 : Matrix A A ℂ), 1, (c : ℂ) • (1 : Matrix (A × B) (A × B) ℂ),
    ⟨hH, isHermitian_one, hH', ?_, ?_, ?_, ?_⟩, rfl⟩
  · show (Γ (_ + s)).PosSemidef
    have : Γ ((c : ℂ) • (1 : Matrix (A × B) (A × B) ℂ) + s) = Γ ((c : ℂ) • 1) + Γ s := rfl
    rw [this, x8_gamma_one]; exact h1
  · have : Γ ((c : ℂ) • (1 : Matrix (A × B) (A × B) ℂ) - s) = Γ ((c : ℂ) • 1) - Γ s := rfl
    rw [this, x8_gamma_one]; exact h2
  · rw [hk]
    have : ((c : ℂ) • (1 : Matrix (A × B) (A × B) ℂ)).PosSemidef :=
      PosSemidef.one.smul (by exact_mod_cast hc)
    exact this.add this
  · rw [hk, sub_self]; exact PosSemidef.zero


theorem x8_feas_psd {s : Matrix (A × B) (A × B) ℂ} {k : Matrix A A ℂ} {l : Matrix B B ℂ}
    {v : Matrix (A × B) (A × B) ℂ} (h : GammaFeasible s k l v) : (Matrix.kronecker k l).PosSemidef := by
  have h2 := (h.2.2.2.2.2.1.add h.2.2.2.2.2.2).smul (show (0 : ℂ) ≤ (1 / 2 : ℂ) by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]; exact Complex.zero_le_real.2 (by norm_num))
  convert h2 using 1
  rw [add_add_sub_cancel, ← two_smul ℂ, smul_smul]
  norm_num

theorem x8_tr_psd {α : Type} [Fintype α] {M : Matrix α α ℂ} (hM : M.PosSemidef) :
    0 ≤ M.trace.re ∧ M.trace.im = 0 := by
  have := hM.trace_nonneg
  rw [Complex.nonneg_iff] at this
  exact ⟨this.1, this.2.symm⟩

theorem x8_G_nonneg {s : Matrix (A × B) (A × B) ℂ} {r : ℝ} (hr : r ∈ x8G s) : 0 ≤ r := by
  obtain ⟨k, l, v, h, rfl⟩ := hr
  exact (x8_tr_psd (x8_feas_psd h)).1

theorem x8_cg_le {s : Matrix (A × B) (A × B) ℂ} {r : ℝ} (hr : r ∈ x8G s) :
    correlationGauge s ≤ (r : EReal) := by
  obtain ⟨k, l, v, h, rfl⟩ := hr
  exact sInf_le ⟨k, l, v, h, rfl⟩

theorem x8_cg_eq (s : Matrix (A × B) (A × B) ℂ) (hne : (x8G s).Nonempty) :
    correlationGauge s = ((sInf (x8G s) : ℝ) : EReal) := by
  have hb : BddBelow (x8G s) := ⟨0, fun r hr => x8_G_nonneg hr⟩
  apply le_antisymm
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    induction c using EReal.rec with
    | bot => exact absurd hc (not_lt_bot)
    | top => exact le_top
    | coe c =>
      have hc' : sInf (x8G s) < c := EReal.coe_lt_coe_iff.1 hc
      obtain ⟨r, hr, hrc⟩ := exists_lt_of_csInf_lt hne hc'
      exact (x8_cg_le hr).trans (EReal.coe_le_coe_iff.2 hrc.le)
  · refine le_sInf ?_
    rintro _ ⟨k, l, v, h, rfl⟩
    exact EReal.coe_le_coe_iff.2 (csInf_le hb ⟨k, l, v, h, rfl⟩)


def x8e : (A × C) × (B × E) → (A × B) × (C × E) := fun i => ((i.1.1, i.2.1), (i.1.2, i.2.2))

theorem x8_bt_sub (X : Matrix (A × B) (A × B) ℂ) (Y : Matrix (C × E) (C × E) ℂ) :
    bipartiteTensor X Y = (Matrix.kronecker X Y).submatrix x8e x8e := rfl

theorem x8_bt_psd {X : Matrix (A × B) (A × B) ℂ} {Y : Matrix (C × E) (C × E) ℂ} (hX : X.PosSemidef)
    (hY : Y.PosSemidef) : (bipartiteTensor X Y).PosSemidef := by
  rw [x8_bt_sub]; exact (hX.kronecker hY).submatrix _

theorem x8_kron_herm {α β : Type} [Fintype α] [Fintype β] {X : Matrix α α ℂ} {Y : Matrix β β ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian) : (Matrix.kronecker X Y).IsHermitian := by
  unfold IsHermitian
  simp only [Matrix.kronecker]
  rw [conjTranspose_kronecker, hX.eq, hY.eq]

theorem x8_bt_herm {X : Matrix (A × B) (A × B) ℂ} {Y : Matrix (C × E) (C × E) ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) : (bipartiteTensor X Y).IsHermitian := by
  rw [x8_bt_sub]; exact (x8_kron_herm hX hY).submatrix _

theorem x8_pm (X v : Matrix (A × B) (A × B) ℂ) (X' v' : Matrix (C × E) (C × E) ℂ)
    (h1 : (X + v).PosSemidef) (h2 : (X - v).PosSemidef) (h3 : (X' + v').PosSemidef)
    (h4 : (X' - v').PosSemidef) :
    (bipartiteTensor X X' + bipartiteTensor v v').PosSemidef ∧
      (bipartiteTensor X X' - bipartiteTensor v v').PosSemidef := by
  have hh : (0 : ℂ) ≤ (1 / 2 : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]; exact Complex.zero_le_real.2 (by norm_num)
  constructor
  · have e : bipartiteTensor X X' + bipartiteTensor v v' = (1 / 2 : ℂ) •
        (bipartiteTensor (X + v) (X' + v') + bipartiteTensor (X - v) (X' - v')) := by
      ext i j; simp only [bipartiteTensor, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rw [e]; exact ((x8_bt_psd h1 h3).add (x8_bt_psd h2 h4)).smul hh
  · have e : bipartiteTensor X X' - bipartiteTensor v v' = (1 / 2 : ℂ) •
        (bipartiteTensor (X + v) (X' - v') + bipartiteTensor (X - v) (X' + v')) := by
      ext i j; simp only [bipartiteTensor, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
    rw [e]; exact ((x8_bt_psd h1 h4).add (x8_bt_psd h2 h3)).smul hh

theorem x8_prod_mem {σ : Matrix (A × B) (A × B) ℂ} {τ : Matrix (C × E) (C × E) ℂ} {r r' : ℝ}
    (hr : r ∈ x8G σ) (hr' : r' ∈ x8G τ) : r * r' ∈ x8G (bipartiteTensor σ τ) := by
  obtain ⟨k, l, v, h, rfl⟩ := hr
  obtain ⟨k', l', v', h', rfl⟩ := hr'
  have hkl : Matrix.kronecker (Matrix.kronecker k k') (Matrix.kronecker l l') =
      bipartiteTensor (Matrix.kronecker k l) (Matrix.kronecker k' l') := by
    ext i j; simp only [bipartiteTensor, Matrix.kronecker, kroneckerMap_apply]; ring
  have hg : ∀ (X : Matrix (A × B) (A × B) ℂ) (Y : Matrix (C × E) (C × E) ℂ),
      Γ (bipartiteTensor X Y) = bipartiteTensor (Γ X) (Γ Y) := fun _ _ => rfl
  obtain ⟨hk, hl, hv, h1, h2, h3, h4⟩ := h
  obtain ⟨hk', hl', hv', h1', h2', h3', h4'⟩ := h'
  have g1 := x8_pm (Γ v) (Γ σ) (Γ v') (Γ τ) h1 h2 h1' h2'
  have g2 := x8_pm _ _ _ _ h3 h4 h3' h4'
  refine ⟨Matrix.kronecker k k', Matrix.kronecker l l', bipartiteTensor v v',
    ⟨x8_kron_herm hk hk', x8_kron_herm hl hl', x8_bt_herm hv hv', ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (Γ (bipartiteTensor v v') + Γ (bipartiteTensor σ τ)).PosSemidef
    rw [hg, hg]; exact g1.1
  · show (Γ (bipartiteTensor v v') - Γ (bipartiteTensor σ τ)).PosSemidef
    rw [hg, hg]; exact g1.2
  · rw [hkl]; exact g2.1
  · rw [hkl]; exact g2.2
  · have i1 := (x8_tr_psd (x8_feas_psd ⟨hk, hl, hv, h1, h2, h3, h4⟩)).2
    have i2 := (x8_tr_psd (x8_feas_psd ⟨hk', hl', hv', h1', h2', h3', h4'⟩)).2
    have : (Matrix.kronecker (Matrix.kronecker k k') (Matrix.kronecker l l')).trace =
        (Matrix.kronecker k l).trace * (Matrix.kronecker k' l').trace := by
      simp only [Matrix.kronecker, trace_kronecker]; ring
    rw [this, Complex.mul_re, i1, i2, zero_mul, sub_zero]


theorem x8_inf_mul (S T : Set ℝ) (hS : S.Nonempty) (hT : T.Nonempty) (hS0 : ∀ r ∈ S, 0 ≤ r)
    (hT0 : ∀ r ∈ T, 0 ≤ r) (g : ℝ) (h : ∀ r ∈ S, ∀ r' ∈ T, g ≤ r * r') : g ≤ sInf S * sInf T := by
  have a0 : 0 ≤ sInf S := le_csInf hS hS0
  have step : ∀ r' ∈ T, g ≤ sInf S * r' := by
    intro r' hr'
    rcases (hT0 r' hr').eq_or_lt with h0 | hpos
    · obtain ⟨r, hr⟩ := hS
      have := h r hr r' hr'
      rw [← h0] at this ⊢; simpa using this
    · have : g / r' ≤ sInf S := le_csInf hS fun r hr => (div_le_iff₀ hpos).2 (h r hr r' hr')
      calc g = g / r' * r' := by field_simp
        _ ≤ sInf S * r' := mul_le_mul_of_nonneg_right this hpos.le
  rcases a0.eq_or_lt with h0 | hpos
  · obtain ⟨r', hr'⟩ := hT
    have := step r' hr'
    rw [← h0] at this ⊢; simpa using this
  · have : g / sInf S ≤ sInf T := le_csInf hT fun r' hr' => (div_le_iff₀' hpos).2 (step r' hr')
    calc g = sInf S * (g / sInf S) := by field_simp
      _ ≤ sInf S * sInf T := mul_le_mul_of_nonneg_left this hpos.le

theorem x8_lb (x : ℝ) : logBits (x : EReal) = if x = 0 then ⊥ else ((Real.logb 2 x : ℝ) : EReal) := by
  unfold logBits
  by_cases h : x = 0
  · simp [h]
  · simp [h, EReal.coe_ne_top, EReal.coe_ne_bot]

theorem x8_log (g a b : ℝ) (hg : 0 ≤ g) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : g ≤ a * b) :
    logBits (g : EReal) ≤ logBits (a : EReal) + logBits (b : EReal) := by
  rcases hg.eq_or_lt with h0 | gpos
  · rw [x8_lb, if_pos h0.symm]; exact bot_le
  have apos : 0 < a := by
    rcases ha.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at h; linarith
    · exact h0
  have bpos : 0 < b := by
    rcases hb.eq_or_lt with h0 | h0
    · rw [← h0, mul_zero] at h; linarith
    · exact h0
  rw [x8_lb, x8_lb, x8_lb, if_neg gpos.ne', if_neg apos.ne', if_neg bpos.ne', ← EReal.coe_add,
    EReal.coe_le_coe_iff, ← Real.logb_mul apos.ne' bpos.ne']
  exact Real.logb_le_logb_of_le (by norm_num) gpos h

theorem x8_gmul (σ : Matrix (A × B) (A × B) ℂ) (τ : Matrix (C × E) (C × E) ℂ)
    (hσ : σ.IsHermitian) (hτ : τ.IsHermitian) :
    (x8G (bipartiteTensor σ τ)).Nonempty ∧
    sInf (x8G (bipartiteTensor σ τ)) ≤ sInf (x8G σ) * sInf (x8G τ) := by
  have n1 := x8_G_ne σ hσ
  have n2 := x8_G_ne τ hτ
  obtain ⟨r, hr⟩ := n1
  obtain ⟨r', hr'⟩ := n2
  refine ⟨⟨_, x8_prod_mem hr hr'⟩, ?_⟩
  refine x8_inf_mul _ _ ⟨r, hr⟩ ⟨r', hr'⟩ (fun _ h => x8_G_nonneg h) (fun _ h => x8_G_nonneg h) _
    fun a ha b hb => csInf_le ⟨0, fun _ h => x8_G_nonneg h⟩ (x8_prod_mem ha hb)

theorem x8_part1 (σ : Matrix (A × B) (A × B) ℂ) (τ : Matrix (C × E) (C × E) ℂ)
    (hσ : σ.IsHermitian) (hτ : τ.IsHermitian) :
    cGamma (bipartiteTensor σ τ) ≤ cGamma σ + cGamma τ := by
  obtain ⟨n3, hle⟩ := x8_gmul σ τ hσ hτ
  have n1 := x8_G_ne σ hσ
  have n2 := x8_G_ne τ hτ
  unfold cGamma
  rw [x8_cg_eq _ n1, x8_cg_eq _ n2, x8_cg_eq _ n3]
  exact x8_log _ _ _ (le_csInf n3 fun _ h => x8_G_nonneg h) (le_csInf n1 fun _ h => x8_G_nonneg h)
    (le_csInf n2 fun _ h => x8_G_nonneg h) hle

end QAlgorithms.Papers.Independent.Dependency50.P18

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder
open Matrix

local notation "Γ" => QAlgorithms.Papers.Independent.Information100.P04.gamma

variable {A B X : Type} [Fintype A] [Fintype B] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq X]

def x8M (y z : X) : Matrix ((A × X) × B) (A × (B × X)) ℂ :=
  fun i j => if i.1.2 = z ∧ j.2.2 = y ∧ i.1.1 = j.1 ∧ i.2 = j.2.1 then 1 else 0

def x8C {m n : Type} [Fintype n] (M : Matrix m n ℂ) (Z : Matrix n n ℂ) : Matrix m m ℂ := M * Z * Mᴴ

def x8N (s : Matrix (A × (B × X)) (A × (B × X)) ℂ) : Matrix ((A × X) × B) ((A × X) × B) ℂ :=
  fun i j => if i.1.2 = j.1.2 then s (i.1.1, (i.2, i.1.2)) (j.1.1, (j.2, j.1.2)) else 0

theorem x8_M_conj (y z : X) (Z : Matrix (A × (B × X)) (A × (B × X)) ℂ) (i j : (A × X) × B) :
    x8C (x8M (A := A) (B := B) y z) Z i j =
      if i.1.2 = z ∧ j.1.2 = z then Z (i.1.1, (i.2, y)) (j.1.1, (j.2, y)) else 0 := by
  obtain ⟨⟨a, x⟩, b⟩ := i
  obtain ⟨⟨a', x'⟩, b'⟩ := j
  simp only [x8C, Matrix.mul_apply, conjTranspose_apply, x8M, Fintype.sum_prod_type]
  by_cases h1 : x = z <;> by_cases h2 : x' = z <;> simp [h1, h2, ite_and, apply_ite (starRingEnd ℂ), mul_ite]


theorem x8_N_sum (Z : Matrix (A × (B × X)) (A × (B × X)) ℂ) :
    x8N Z = ∑ z, x8C (x8M (A := A) (B := B) z z) Z := by
  ext ⟨⟨a, x⟩, b⟩ ⟨⟨a', x'⟩, b'⟩
  rw [Matrix.sum_apply]
  simp_rw [x8_M_conj]
  by_cases h : x = x'
  · subst h; simp [x8N, ite_and]
  · simp [x8N, h, ite_and]
    intro hx; subst hx; exact absurd rfl h

theorem x8_N_psd {Z : Matrix (A × (B × X)) (A × (B × X)) ℂ} (hZ : Z.PosSemidef) : (x8N Z).PosSemidef := by
  rw [x8_N_sum]; exact posSemidef_sum _ fun z _ => hZ.mul_mul_conjTranspose_same _

theorem x8_M_kraus : ∑ z : X, (x8M (A := A) (B := B) z z)ᴴ * x8M (A := A) (B := B) z z = 1 := by
  ext ⟨a, b, x⟩ ⟨a', b', x'⟩
  rw [Matrix.sum_apply]
  simp only [Matrix.mul_apply, conjTranspose_apply, x8M, Fintype.sum_prod_type, Matrix.one_apply]
  by_cases h1 : a = a' <;> by_cases h2 : b = b' <;> by_cases h3 : x = x' <;>
    simp [h1, h2, h3, ite_and, apply_ite (starRingEnd ℂ), mul_ite, eq_comm]

theorem x8_N_channel : QAlgorithms.IsChannel (x8N (A := A) (B := B) (X := X)) := by
  let e := Fintype.equivFin X
  refine ⟨Fintype.card X, fun n => x8M (A := A) (B := B) (e.symm n) (e.symm n), ?_, fun ρ => ?_⟩
  · unfold QAlgorithms.IsKrausFamily
    rw [← x8_M_kraus (A := A) (B := B) (X := X)]
    exact Equiv.sum_comp e.symm (fun z => (x8M (A := A) (B := B) z z)ᴴ * x8M (A := A) (B := B) z z)
  · unfold QAlgorithms.krausApply
    rw [x8_N_sum]
    exact (Equiv.sum_comp e.symm (fun z => x8C (x8M (A := A) (B := B) z z) ρ)).symm

def x8l (l : Matrix (B × X) (B × X) ℂ) : Matrix B B ℂ := fun b b' => ∑ y, l (b, y) (b', y)

theorem x8_kl (k : Matrix A A ℂ) (l : Matrix (B × X) (B × X) ℂ) :
    Matrix.kronecker (Matrix.kronecker k (1 : Matrix X X ℂ)) (x8l l) =
      ∑ y, ∑ z, x8C (x8M (A := A) (B := B) y z) (Matrix.kronecker k l) := by
  ext ⟨⟨a, x⟩, b⟩ ⟨⟨a', x'⟩, b'⟩
  rw [Matrix.sum_apply]
  simp_rw [Matrix.sum_apply, x8_M_conj]
  simp only [Matrix.kronecker, kroneckerMap_apply, Matrix.one_apply, x8l, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases h : x = x'
  · subst h; simp [ite_and]
  · simp [h, ite_and]
    intro hx; subst hx; exact absurd rfl h

theorem x8_N_gamma (Y : Matrix (A × (B × X)) (A × (B × X)) ℂ) : Γ (x8N Y) = x8N (Γ Y) := by
  ext ⟨⟨a, x⟩, b⟩ ⟨⟨a', x'⟩, b'⟩
  simp only [QAlgorithms.Papers.Independent.Information100.P04.gamma, x8N]
  by_cases h : x = x'
  · subst h; simp
  · simp [h]

theorem x8_N_herm {Y : Matrix (A × (B × X)) (A × (B × X)) ℂ} (hY : Y.IsHermitian) : (x8N Y).IsHermitian := by
  ext ⟨⟨a, x⟩, b⟩ ⟨⟨a', x'⟩, b'⟩
  simp only [conjTranspose_apply, x8N]
  by_cases h : x = x'
  · subst h; simp; exact hY.apply _ _
  · simp [h, Ne.symm h]

theorem x8_l_herm {l : Matrix (B × X) (B × X) ℂ} (hl : l.IsHermitian) : (x8l l).IsHermitian := by
  ext b b'
  simp only [conjTranspose_apply, x8l, star_sum]
  exact Finset.sum_congr rfl fun y _ => hl.apply _ _

theorem x8_N_add (Y W : Matrix (A × (B × X)) (A × (B × X)) ℂ) : x8N (Y + W) = x8N Y + x8N W := by
  ext i j; simp only [x8N, Matrix.add_apply]; split_ifs <;> simp

theorem x8_N_sub (Y W : Matrix (A × (B × X)) (A × (B × X)) ℂ) : x8N (Y - W) = x8N Y - x8N W := by
  ext i j; simp only [x8N, Matrix.sub_apply]; split_ifs <;> simp


theorem x8_C_add {m n : Type} [Fintype n] (M : Matrix m n ℂ) (Z W : Matrix n n ℂ) :
    x8C M (Z + W) = x8C M Z + x8C M W := by
  simp only [x8C, Matrix.mul_add, Matrix.add_mul]

theorem x8_C_sub {m n : Type} [Fintype n] (M : Matrix m n ℂ) (Z W : Matrix n n ℂ) :
    x8C M (Z - W) = x8C M Z - x8C M W := by
  simp only [x8C, Matrix.mul_sub, Matrix.sub_mul]

theorem x8_C_psd {m n : Type} [Fintype m] [Fintype n] (M : Matrix m n ℂ) {Z : Matrix n n ℂ} (hZ : Z.PosSemidef) :
    (x8C M Z).PosSemidef := hZ.mul_mul_conjTranspose_same M

theorem x8_C_ite {m n : Type} [Fintype n] (M : Matrix m n ℂ) (c : Prop) [Decidable c] (Z : Matrix n n ℂ) :
    x8C M (if c then Z else 0) = if c then x8C M Z else 0 := by
  split_ifs <;> simp [x8C]

theorem x8_N_diag (v : Matrix (A × (B × X)) (A × (B × X)) ℂ) :
    ∑ y, ∑ z, x8C (x8M (A := A) (B := B) y z) (if y = z then v else 0) = x8N v := by
  rw [x8_N_sum]
  simp_rw [x8_C_ite, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem x8_N_mem {s : Matrix (A × (B × X)) (A × (B × X)) ℂ} {r : ℝ} (hr : r ∈ x8G s) :
    (Fintype.card X : ℝ) * r ∈ x8G (x8N s) := by
  obtain ⟨k, l, v, h, rfl⟩ := hr
  have hkl := x8_feas_psd h
  obtain ⟨hk, hl, hv, h1, h2, h3, h4⟩ := h
  refine ⟨Matrix.kronecker k (1 : Matrix X X ℂ), x8l l, x8N v,
    ⟨x8_kron_herm hk isHermitian_one, x8_l_herm hl, x8_N_herm hv, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← x8_N_add, x8_N_gamma]; exact x8_N_psd h1
  · rw [← x8_N_sub, x8_N_gamma]; exact x8_N_psd h2
  · rw [x8_kl, ← x8_N_diag, ← Finset.sum_add_distrib]
    refine posSemidef_sum _ fun y _ => ?_
    rw [← Finset.sum_add_distrib]
    refine posSemidef_sum _ fun z _ => ?_
    rw [← x8_C_add]
    refine x8_C_psd _ ?_
    split_ifs
    · exact h3
    · rw [add_zero]; exact hkl
  · rw [x8_kl, ← x8_N_diag, ← Finset.sum_sub_distrib]
    refine posSemidef_sum _ fun y _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine posSemidef_sum _ fun z _ => ?_
    rw [← x8_C_sub]
    refine x8_C_psd _ ?_
    split_ifs
    · exact h4
    · rw [sub_zero]; exact hkl
  · have htl : (x8l l).trace = l.trace := by
      simp only [x8l, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
    simp only [Matrix.kronecker, trace_kronecker, trace_one, htl]
    rw [show k.trace * (Fintype.card X : ℂ) * l.trace = ((Fintype.card X : ℝ) : ℂ) * (k.trace * l.trace) by
      push_cast; ring, Complex.re_ofReal_mul]

theorem x8_N_le [Nonempty X] (s : Matrix (A × (B × X)) (A × (B × X)) ℂ) (hs : s.IsHermitian) :
    (x8G (x8N s)).Nonempty ∧ sInf (x8G (x8N s)) ≤ (Fintype.card X : ℝ) * sInf (x8G s) := by
  have n1 := x8_G_ne s hs
  obtain ⟨r, hr⟩ := n1
  refine ⟨⟨_, x8_N_mem hr⟩, ?_⟩
  have cpos : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have : sInf (x8G (x8N s)) / (Fintype.card X : ℝ) ≤ sInf (x8G s) := by
    refine le_csInf ⟨r, hr⟩ fun r' hr' => ?_
    rw [div_le_iff₀' cpos]
    exact csInf_le ⟨0, fun _ h => x8_G_nonneg h⟩ (x8_N_mem hr')
  rwa [div_le_iff₀' cpos] at this


section
variable {A' B' : Type} [Fintype A'] [Fintype B'] [DecidableEq A'] [DecidableEq B']
theorem x8_scale_mem {s : Matrix (A' × B') (A' × B') ℂ} {r t : ℝ} (hr : r ∈ x8G s) (ht : 0 < t) :
    t * r ∈ x8G ((t : ℂ) • s) := by
  obtain ⟨k, l, v, ⟨hk, hl, hv, h1, h2, h3, h4⟩, rfl⟩ := hr
  have ht' : (0 : ℂ) ≤ (t : ℂ) := Complex.zero_le_real.2 ht.le
  have hsm : ∀ Y : Matrix (A' × B') (A' × B') ℂ, Γ ((t : ℂ) • Y) = (t : ℂ) • Γ Y := fun Y => by
    ext i j; rfl
  have hkr : Matrix.kronecker k ((t : ℂ) • l) = (t : ℂ) • Matrix.kronecker k l := by
    simp only [Matrix.kronecker]; rw [kronecker_smul]
  refine ⟨k, (t : ℂ) • l, (t : ℂ) • v, ⟨hk, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [IsHermitian, conjTranspose_smul, hl.eq]
  · simp [IsHermitian, conjTranspose_smul, hv.eq]
  · rw [← smul_add, hsm]; exact h1.smul ht'
  · rw [← smul_sub, hsm]; exact h2.smul ht'
  · rw [hkr, ← smul_add]; exact h3.smul ht'
  · rw [hkr, ← smul_sub]; exact h4.smul ht'
  · rw [hkr, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

end

theorem x8_N_trace (Y : Matrix (A × (B × X)) (A × (B × X)) ℂ) : (x8N Y).trace = Y.trace := by
  simp only [Matrix.trace, Matrix.diag, x8N, if_true, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm

theorem x8_log2 (g b c : ℝ) (hg : 0 ≤ g) (hb : 0 ≤ b) (hc : 0 < c) (h : g ≤ c * b) :
    logBits (g : EReal) ≤ ((Real.logb 2 c : ℝ) : EReal) + logBits (b : EReal) := by
  rcases hg.eq_or_lt with h0 | gpos
  · rw [x8_lb, if_pos h0.symm]; exact bot_le
  have bpos : 0 < b := by
    rcases hb.eq_or_lt with h0 | h0
    · rw [← h0, mul_zero] at h; linarith
    · exact h0
  rw [x8_lb, x8_lb, if_neg gpos.ne', if_neg bpos.ne', ← EReal.coe_add,
    EReal.coe_le_coe_iff, ← Real.logb_mul hc.ne' bpos.ne']
  exact Real.logb_le_logb_of_le (by norm_num) gpos h

end QAlgorithms.Papers.Independent.Dependency50.P18

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder
open Matrix

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]


def x8J (x : X) : Matrix (A × (B × X)) (A × B) ℂ :=
  fun i j => if i.1 = j.1 ∧ i.2.1 = j.2 ∧ i.2.2 = x then 1 else 0

theorem x8_cqR (p : X → ℝ) (rho : X → Matrix (A × B) (A × B) ℂ) :
    cqRight p rho = ∑ x, x8C (x8J (A := A) (B := B) x) ((p x : ℂ) • rho x) := by
  ext ⟨a, b, x⟩ ⟨a', b', x'⟩
  rw [Matrix.sum_apply]
  simp only [cqRight, x8C, x8J, Matrix.mul_apply, conjTranspose_apply, Fintype.sum_prod_type]
  by_cases h : x = x'
  · subst h; simp [ite_and, apply_ite (starRingEnd ℂ), mul_ite]
  · simp [h, ite_and, apply_ite (starRingEnd ℂ), mul_ite]

theorem x8_cqR_dens (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (rho : X → Matrix (A × B) (A × B) ℂ) (hrho : ∀ x, QAlgorithms.IsDensityMatrix (rho x)) :
    QAlgorithms.IsDensityMatrix (cqRight p rho) := by
  refine ⟨?_, ?_⟩
  · rw [x8_cqR]
    exact posSemidef_sum _ fun x _ => x8_C_psd _ ((hrho x).1.smul (Complex.zero_le_real.2 (hp x)))
  · have : Matrix.trace (cqRight p rho : Matrix (A × (B × X)) (A × (B × X)) ℂ) =
        ∑ x, (p x : ℂ) * (rho x).trace := by
      simp only [Matrix.trace, Matrix.diag, cqRight, if_true, Fintype.sum_prod_type, Finset.mul_sum]
      conv_lhs => arg 2; ext; rw [Finset.sum_comm]
      conv_lhs => rw [Finset.sum_comm]
    rw [this]
    simp_rw [(hrho _).2, mul_one]
    exact_mod_cast hsum

theorem x8_cqL (p : X → ℝ) (rho : X → Matrix (A × B) (A × B) ℂ) :
    cqLeft p rho = x8N (cqRight p rho) := by
  ext ⟨⟨a, x⟩, b⟩ ⟨⟨a', x'⟩, b'⟩
  simp only [cqLeft, cqRight, x8N]
  by_cases h : x = x' <;> simp [h]

/-- Proposition 7, PDF p.3, (17)–(19), Appendix E pp.9–10.
The cost is the full alphabet dimension, without independence or positive-probability assumptions. -/
theorem x8_main (D : Divergence) (hD : IsGeneralizedDivergence D)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (rho : X → Matrix (A × B) (A × B) ℂ)
    (hrho : ∀ x, QAlgorithms.IsDensityMatrix (rho x)) :
    cGamma (cqLeft p rho) ≤ (Real.logb 2 (Fintype.card X) : EReal) + cGamma (cqRight p rho) ∧
    capitalGamma D (cqLeft p rho) ≤ (Real.logb 2 (Fintype.card X) : EReal) +
      capitalGamma D (cqRight p rho) := by
  have hR := x8_cqR_dens p hp hsum rho hrho
  have hL : QAlgorithms.IsDensityMatrix (x8N (cqRight p rho)) :=
    ⟨x8_N_psd hR.1, by rw [x8_N_trace]; exact hR.2⟩
  have cpos : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  rw [x8_cqL]
  refine ⟨?_, ?_⟩
  · obtain ⟨n3, hle⟩ := x8_N_le (cqRight p rho) hR.1.1
    have n1 := x8_G_ne (cqRight p rho) hR.1.1
    unfold cGamma
    rw [x8_cg_eq _ n3, x8_cg_eq _ n1]
    exact x8_log2 _ _ _ (le_csInf n3 fun _ h => x8_G_nonneg h) (le_csInf n1 fun _ h => x8_G_nonneg h)
      cpos hle
  · refine EReal.le_add_of_forall_gt (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)) ?_
    intro a' ha' b' hb'
    obtain ⟨_, ⟨σ', hσ', hγ, rfl⟩, hy⟩ := sInf_lt_iff.1 hb'
    set t : ℝ := (Fintype.card X : ℝ)⁻¹
    have tpos : 0 < t := inv_pos.2 cpos
    have hγ' : correlationGauge ((t : ℂ) • x8N σ') ≤ 1 := by
      refine le_trans ?_ hγ
      refine le_sInf ?_
      rintro _ ⟨k, l, v, h, rfl⟩
      have hm := x8_scale_mem (x8_N_mem ⟨k, l, v, h, rfl⟩) tpos
      rw [show t * ((Fintype.card X : ℝ) * (Matrix.kronecker k l).trace.re) =
        (Matrix.kronecker k l).trace.re by rw [← mul_assoc, inv_mul_cancel₀ cpos.ne', one_mul]] at hm
      exact x8_cg_le hm
    have hdp := hD.dataProcessing _ _ _ hR hσ' x8_N_channel
    have hsc := hD.scaling (x8N (cqRight p rho)) (x8N σ') t hL (x8_N_psd hσ') tpos
    have key : D (x8N (cqRight p rho)) ((t : ℂ) • x8N σ') ≤ a' + b' := by
      rw [hsc, Real.logb_inv, EReal.coe_neg, sub_eq_add_neg, neg_neg, add_comm]
      exact add_le_add ha'.le (hdp.trans hy.le)
    refine le_trans (sInf_le ⟨(t : ℂ) • x8N σ', (x8_N_psd hσ').smul (Complex.zero_le_real.2 tpos.le),
      hγ', rfl⟩) ?_
    convert key using 2

end QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Dependency50.P18 in
theorem solution {A B X : Type}
  [Fintype A] [Fintype B] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty X]
  (D : Divergence) (hD : IsGeneralizedDivergence D)
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (rho : X → Matrix (A × B) (A × B) ℂ)
    (hrho : ∀ x, QAlgorithms.IsDensityMatrix (rho x)) :
    cGamma (cqLeft p rho) ≤ (Real.logb 2 (Fintype.card X) : EReal) + cGamma (cqRight p rho) ∧
    capitalGamma D (cqLeft p rho) ≤ (Real.logb 2 (Fintype.card X) : EReal) +
      capitalGamma D (cqRight p rho) :=
  x8_main D hD p hp hsum rho hrho
