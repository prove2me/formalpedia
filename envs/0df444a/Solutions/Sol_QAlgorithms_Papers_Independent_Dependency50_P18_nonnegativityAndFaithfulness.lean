-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P18.nonnegativityAndFaithfulness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:14:22.621383+00:00
-- url     : https://prove2.me/submissions/d906fee6-a446-42b2-8f1d-b6be1f5fa88c

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

local notation "Γ" => QAlgorithms.Papers.Independent.Information100.P04.gamma

theorem x8_entry_le {α : Type} [Fintype α] [DecidableEq α] {P : Matrix α α ℂ} (hP : P.PosSemidef)
    (i j : α) : ‖P i j‖ ≤ P.trace.re := by
  set U := (hP.1.eigenvectorUnitary : Matrix α α ℂ)
  have hs : P = U * diagonal (fun k => ((hP.1.eigenvalues k : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hP.1.spectral_theorem]
    rfl
  have hU : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hrow : ∀ i k, ‖U i k‖ ≤ 1 := by
    intro i k
    have h1 : ∑ k, ‖U i k‖ ^ 2 = 1 := by
      have := congrFun (congrFun hU i) i
      simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply_eq] at this
      have h2 : ∑ k, ((‖U i k‖ ^ 2 : ℝ) : ℂ) = 1 := by
        rw [← this]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      exact_mod_cast h2
    have : ‖U i k‖ ^ 2 ≤ 1 := by
      rw [← h1]
      exact Finset.single_le_sum (f := fun k => ‖U i k‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)
    nlinarith [norm_nonneg (U i k)]
  have hent : P i j = ∑ k, U i k * ((hP.1.eigenvalues k : ℝ) : ℂ) * star (U j k) := by
    conv_lhs => rw [hs]
    simp [Matrix.mul_apply, diagonal, conjTranspose_apply]
  have htr : P.trace.re = ∑ k, hP.1.eigenvalues k := by
    rw [hP.1.trace_eq_sum_eigenvalues]
    simp
  rw [hent, htr]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hP.eigenvalues_nonneg k)]
  have := hP.eigenvalues_nonneg k
  calc ‖U i k‖ * hP.1.eigenvalues k * ‖U j k‖ ≤ 1 * hP.1.eigenvalues k * 1 := by
        gcongr
        · exact hrow i k
        · exact hrow j k
    _ = hP.1.eigenvalues k := by ring


variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem x8_trG (Y : Matrix (A × B) (A × B) ℂ) : (Γ Y).trace = Y.trace := rfl

theorem x8_feas_tr {s : Matrix (A × B) (A × B) ℂ} {k : Matrix A A ℂ} {l : Matrix B B ℂ}
    {v : Matrix (A × B) (A × B) ℂ} (h : GammaFeasible s k l v) :
    s.trace.re ≤ v.trace.re ∧ v.trace.re ≤ (Matrix.kronecker k l).trace.re := by
  have h1 := (x8_tr_psd h.2.2.2.2.1).1
  have h2 := (x8_tr_psd h.2.2.2.2.2.2).1
  rw [x8_trG, trace_sub, Complex.sub_re] at h1
  rw [trace_sub, Complex.sub_re] at h2
  constructor <;> linarith

theorem x8_feas_entry {s : Matrix (A × B) (A × B) ℂ} {k : Matrix A A ℂ} {l : Matrix B B ℂ}
    {v : Matrix (A × B) (A × B) ℂ} (h : GammaFeasible s k l v) (i j : A × B) :
    ‖Matrix.kronecker k l i j - s i j‖ ≤ (Matrix.kronecker k l).trace.re - s.trace.re := by
  have e1 := x8_entry_le h.2.2.2.2.2.2 i j
  have e2 := x8_entry_le h.2.2.2.2.1 (i.1, j.2) (j.1, i.2)
  have hv : (Γ (v - s)) (i.1, j.2) (j.1, i.2) = v i j - s i j := rfl
  rw [hv, x8_trG, trace_sub, Complex.sub_re] at e2
  rw [Matrix.sub_apply, trace_sub, Complex.sub_re] at e1
  calc ‖Matrix.kronecker k l i j - s i j‖ = ‖(Matrix.kronecker k l i j - v i j) + (v i j - s i j)‖ := by
        ring_nf
    _ ≤ ‖Matrix.kronecker k l i j - v i j‖ + ‖v i j - s i j‖ := norm_add_le _ _
    _ ≤ _ := by linarith

def x8pA (M : Matrix (A × B) (A × B) ℂ) : Matrix A A ℂ := fun a a' => ∑ b, M (a, b) (a', b)
def x8pB (M : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ := fun b b' => ∑ a, M (a, b) (a, b')

theorem x8_poly (k : Matrix A A ℂ) (l : Matrix B B ℂ) (i j : A × B) :
    Matrix.kronecker k l i j * (Matrix.kronecker k l).trace =
      Matrix.kronecker (x8pA (Matrix.kronecker k l)) (x8pB (Matrix.kronecker k l)) i j := by
  have h1 : x8pA (Matrix.kronecker k l) = l.trace • k := by
    ext a a'
    simp only [x8pA, Matrix.kronecker, kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul, Matrix.trace,
      Matrix.diag, ← Finset.mul_sum]
    ring
  have h2 : x8pB (Matrix.kronecker k l) = k.trace • l := by
    ext b b'
    simp only [x8pB, Matrix.kronecker, kroneckerMap_apply, Matrix.smul_apply, smul_eq_mul, Matrix.trace,
      Matrix.diag, ← Finset.sum_mul]
  rw [h1, h2]
  simp only [Matrix.kronecker, kroneckerMap_apply, trace_kronecker, Matrix.smul_apply, smul_eq_mul]
  ring

def x8Eb (b : B) : Matrix A (A × B) ℂ := fun a i => if i = (a, b) then 1 else 0

theorem x8_pA_sum (M : Matrix (A × B) (A × B) ℂ) : x8pA M = ∑ b, x8C (x8Eb (A := A) b) M := by
  ext a a'
  rw [Matrix.sum_apply]
  simp [x8pA, x8C, x8Eb, Matrix.mul_apply, conjTranspose_apply, apply_ite (starRingEnd ℂ)]

def x8Ea (a : A) : Matrix B (A × B) ℂ := fun b i => if i = (a, b) then 1 else 0

theorem x8_pB_sum (M : Matrix (A × B) (A × B) ℂ) : x8pB M = ∑ a, x8C (x8Ea (B := B) a) M := by
  ext b b'
  rw [Matrix.sum_apply]
  simp [x8pB, x8C, x8Ea, Matrix.mul_apply, conjTranspose_apply, apply_ite (starRingEnd ℂ)]

theorem x8_pA_dens {M : Matrix (A × B) (A × B) ℂ} (hM : QAlgorithms.IsDensityMatrix M) :
    QAlgorithms.IsDensityMatrix (x8pA M) := by
  refine ⟨?_, ?_⟩
  · rw [x8_pA_sum]; exact posSemidef_sum _ fun b _ => x8_C_psd _ hM.1
  · rw [← hM.2]
    simp only [x8pA, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]

theorem x8_pB_dens {M : Matrix (A × B) (A × B) ℂ} (hM : QAlgorithms.IsDensityMatrix M) :
    QAlgorithms.IsDensityMatrix (x8pB M) := by
  refine ⟨?_, ?_⟩
  · rw [x8_pB_sum]; exact posSemidef_sum _ fun b _ => x8_C_psd _ hM.1
  · rw [← hM.2]
    simp only [x8pB, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
    exact Finset.sum_comm

theorem x8_LL (ρ : Matrix (A × B) (A × B) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (M : ℕ → Matrix (A × B) (A × B) ℂ) (hM : ∀ n, ∃ k l, M n = Matrix.kronecker k l)
    (hlim : Filter.Tendsto M Filter.atTop (nhds ρ)) : IsProductState ρ := by
  refine ⟨x8pA ρ, x8pB ρ, x8_pA_dens hρ, x8_pB_dens hρ, ?_⟩
  ext i j
  have hf : Continuous fun N : Matrix (A × B) (A × B) ℂ =>
      N i j * N.trace - Matrix.kronecker (x8pA N) (x8pB N) i j := by
    simp only [Matrix.kronecker, kroneckerMap_apply, x8pA, x8pB, Matrix.trace, Matrix.diag]
    fun_prop
  have h0 : ∀ n, (fun N : Matrix (A × B) (A × B) ℂ =>
      N i j * N.trace - Matrix.kronecker (x8pA N) (x8pB N) i j) (M n) = 0 := by
    intro n
    obtain ⟨k, l, hkl⟩ := hM n
    simp only [hkl, x8_poly, sub_self]
  have := (hf.tendsto ρ).comp hlim
  have h1 : (fun N : Matrix (A × B) (A × B) ℂ =>
      N i j * N.trace - Matrix.kronecker (x8pA N) (x8pB N) i j) ρ = 0 := by
    refine tendsto_nhds_unique this ?_
    simp only [Function.comp_def, h0]
    exact tendsto_const_nhds
  simp only [hρ.2, mul_one, sub_eq_zero] at h1
  exact h1


theorem x8_tr_le_g {s : Matrix (A × B) (A × B) ℂ} (hne : (x8G s).Nonempty) :
    s.trace.re ≤ sInf (x8G s) :=
  le_csInf hne fun _ ⟨_, _, _, h, e⟩ => e ▸ (x8_feas_tr h).1.trans (x8_feas_tr h).2

theorem x8_LL2 (ρ : Matrix (A × B) (A × B) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (σ : ℕ → Matrix (A × B) (A × B) ℂ) (hσ : ∀ n, (σ n).IsHermitian)
    (hγ : ∀ n, correlationGauge (σ n) ≤ 1)
    (hlim : Filter.Tendsto σ Filter.atTop (nhds ρ)) : IsProductState ρ := by
  have hw : ∀ n : ℕ, ∃ k l v, GammaFeasible (σ n) k l v ∧
      (Matrix.kronecker k l).trace.re < 1 + 1 / ((n : ℝ) + 1) := by
    intro n
    have hne := x8_G_ne (σ n) (hσ n)
    have h1 := hγ n
    rw [x8_cg_eq _ hne, show (1 : EReal) = ((1 : ℝ) : EReal) from rfl, EReal.coe_le_coe_iff] at h1
    have : sInf (x8G (σ n)) < 1 + 1 / ((n : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨r, ⟨k, l, v, h, rfl⟩, hr⟩ := exists_lt_of_csInf_lt hne this
    exact ⟨k, l, v, h, hr⟩
  choose k l v hf ht using hw
  refine x8_LL ρ hρ (fun n => Matrix.kronecker (k n) (l n)) (fun n => ⟨k n, l n, rfl⟩) ?_
  have htr : Filter.Tendsto (fun n => (σ n).trace.re) Filter.atTop (nhds 1) := by
    have hc : Continuous fun N : Matrix (A × B) (A × B) ℂ => N.trace.re := by
      simp only [Matrix.trace, Matrix.diag]; fun_prop
    have := (hc.tendsto ρ).comp hlim
    rwa [hρ.2, Complex.one_re] at this
  have hd : Filter.Tendsto (fun n => Matrix.kronecker (k n) (l n) - σ n) Filter.atTop (nhds 0) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    rw [show (0 : Matrix (A × B) (A × B) ℂ) i j = 0 from rfl, tendsto_zero_iff_norm_tendsto_zero]
    have hb : Filter.Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1) - (σ n).trace.re) Filter.atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
      have := this.sub htr
      simpa using this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hb
    have := x8_feas_entry (hf n) i j
    simp only [Matrix.sub_apply, Pi.zero_apply]
    linarith [ht n]
  have := hd.add hlim
  simpa using this

end QAlgorithms.Papers.Independent.Dependency50.P18

end

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder
open Matrix

local notation "Γ" => QAlgorithms.Papers.Independent.Information100.P04.gamma

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def x8T : QAlgorithms.Superop (A × B) Unit := fun X => fun _ _ => X.trace

def x8Et (i : A × B) : Matrix Unit (A × B) ℂ := fun _ j => if j = i then 1 else 0

theorem x8_T_channel : QAlgorithms.IsChannel (x8T (A := A) (B := B)) := by
  let e := Fintype.equivFin (A × B)
  refine ⟨Fintype.card (A × B), fun n => x8Et (e.symm n), ?_, fun ρ => ?_⟩
  · unfold QAlgorithms.IsKrausFamily
    rw [Equiv.sum_comp e.symm (fun i => (x8Et i)ᴴ * x8Et i)]
    ext p q
    rw [Matrix.sum_apply]
    simp [x8Et, Matrix.mul_apply, conjTranspose_apply, apply_ite (starRingEnd ℂ), Matrix.one_apply]
  · unfold QAlgorithms.krausApply
    rw [Equiv.sum_comp e.symm (fun i => x8Et i * ρ * (x8Et i)ᴴ)]
    ext u u'
    rw [Matrix.sum_apply]
    simp [x8T, x8Et, Matrix.mul_apply, conjTranspose_apply, apply_ite (starRingEnd ℂ), Matrix.trace]

theorem x8_D_lower (D : Divergence) (hD : IsGeneralizedDivergence D) [Nonempty A] [Nonempty B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ)
    (σ : Matrix (A × B) (A × B) ℂ) (hσ : σ.PosSemidef) (c : ℝ) (hc : 0 < c) (htr : σ.trace = (c : ℂ)) :
    ((-Real.logb 2 c : ℝ) : EReal) ≤ D ρ σ := by
  have hdp := hD.dataProcessing ρ σ x8T hρ hσ x8_T_channel
  have e1 : x8T ρ = (1 : Matrix Unit Unit ℂ) := by
    ext u u'; simp [x8T, hρ.2]
  have e2 : x8T σ = ((c : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ) := by
    ext u u'; simp [x8T, htr]
  have d1 : QAlgorithms.IsDensityMatrix (1 : Matrix Unit Unit ℂ) := ⟨PosSemidef.one, by simp⟩
  rw [e1, e2, hD.scaling _ _ c d1 PosSemidef.one hc, hD.zeroValue _ d1, zero_sub, ← EReal.coe_neg] at hdp
  exact hdp

theorem x8_D_zero (D : Divergence) (hD : IsGeneralizedDivergence D) [Nonempty A] [Nonempty B]
    (ρ : Matrix (A × B) (A × B) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) (h0 : 0 ≤ D ρ 0) :
    D ρ 0 = ⊤ := by
  have hs := hD.scaling ρ 0 2 hρ PosSemidef.zero two_pos
  rw [smul_zero, Real.logb_self_eq_one (by norm_num)] at hs
  revert hs h0
  generalize D ρ 0 = x
  intro h0 hs
  induction x using EReal.rec with
  | bot => exact absurd h0 (by simp)
  | top => rfl
  | coe r =>
    exfalso
    rw [← EReal.coe_sub, EReal.coe_eq_coe_iff] at hs
    linarith

theorem x8_prod_one {ρ : Matrix (A × B) (A × B) ℂ} (h : IsProductState ρ) : (1 : ℝ) ∈ x8G ρ := by
  obtain ⟨s, t, hs, ht, rfl⟩ := h
  have hg : Γ (Matrix.kronecker s t) = Matrix.kronecker s tᵀ := rfl
  refine ⟨s, t, Matrix.kronecker s t, ⟨hs.1.1, ht.1.1, (hs.1.kronecker ht.1).1, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (Γ (Matrix.kronecker s t) + Γ (Matrix.kronecker s t)).PosSemidef
    rw [hg]; exact (hs.1.kronecker ht.1.transpose).add (hs.1.kronecker ht.1.transpose)
  · rw [sub_self]; exact PosSemidef.zero
  · exact (hs.1.kronecker ht.1).add (hs.1.kronecker ht.1)
  · rw [sub_self]; exact PosSemidef.zero
  · simp only [Matrix.kronecker, trace_kronecker, hs.2, ht.2, mul_one, Complex.one_re]

def x8K : Set (Matrix (A × B) (A × B) ℂ) := {σ | σ.PosSemidef ∧ σ.trace.re ≤ 1}

theorem x8_K_compact : IsCompact (x8K (A := A) (B := B)) := by
  have hK : IsCompact (Set.univ.pi fun _ : A × B =>
      Set.univ.pi fun _ : A × B => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hK.of_isClosed_subset ?_ ?_
  · have e : x8K (A := A) (B := B) =
        {X | Xᴴ = X} ∩ (⋂ x : A × B → ℂ, {X | 0 ≤ star x ⬝ᵥ X *ᵥ x}) ∩ {X | X.trace.re ≤ 1} := by
      ext X
      simp only [x8K, Matrix.posSemidef_iff_dotProduct_mulVec, Set.mem_setOf_eq,
        Set.mem_inter_iff, Set.mem_iInter, Matrix.IsHermitian, and_assoc]
    rw [e]
    refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
    · have e2 : {X : Matrix (A × B) (A × B) ℂ | Xᴴ = X} = ⋂ i, ⋂ j, {X | star (X j i) = X i j} := by
        ext X
        simp only [Set.mem_setOf_eq, Set.mem_iInter, ← Matrix.ext_iff, conjTranspose_apply]
      rw [e2]
      exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)
    · exact isClosed_iInter fun x => isClosed_le continuous_const (by fun_prop)
    · refine isClosed_le ?_ continuous_const
      simp only [Matrix.trace, Matrix.diag]; fun_prop
  · intro X hX
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    exact fun p q => (x8_entry_le hX.1 p q).trans hX.2

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

/-- Proposition 4, PDF p.3, (14), Appendix C pp.8–9: every clause is retained.
Printed: the three Section II laws suffice, without a zero-comparison condition.
Changed: assume only `0 ≤ D rho 0` for this input state. Why: the printed laws allow
D(rho||0)=-infinity, and zero is feasible in (4), contradicting nonnegativity.
This is the necessary boundary condition, not positivity on arbitrary comparisons;
Umegaki and sandwiched divergences satisfy it. Independent moderation is required.
Faithfulness and lower semicontinuity of D are premises only of the final implication. -/
theorem x8_main (D : Divergence) (hD : IsGeneralizedDivergence D)
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hzeroComparison : 0 ≤ D rho 0) :
    0 ≤ cGamma rho ∧ 0 ≤ capitalGamma D rho ∧
    (IsProductState rho → cGamma rho = 0 ∧ capitalGamma D rho = 0) ∧
    (cGamma rho = 0 → IsProductState rho) ∧
    (DivergenceFaithful D → DivergenceLowerSemicontinuous D →
      capitalGamma D rho = 0 → IsProductState rho) := by
  have hne := x8_G_ne rho hrho.1.1
  set g := sInf (x8G rho) with hg_def
  have hg1 : 1 ≤ g := by
    have := x8_tr_le_g hne; rwa [hrho.2, Complex.one_re] at this
  have hcg : cGamma rho = ((Real.logb 2 g : ℝ) : EReal) := by
    unfold cGamma; rw [x8_cg_eq _ hne, x8_lb, if_neg (by linarith)]
  have htrle : ∀ σ : Matrix (A × B) (A × B) ℂ, σ.PosSemidef → correlationGauge σ ≤ 1 → σ.trace.re ≤ 1 := by
    intro σ hσ hγ
    have hneσ := x8_G_ne σ hσ.1
    have := x8_tr_le_g hneσ
    rw [x8_cg_eq _ hneσ, show (1 : EReal) = ((1 : ℝ) : EReal) from rfl, EReal.coe_le_coe_iff] at hγ
    linarith
  have hpos : 0 ≤ capitalGamma D rho := by
    refine le_sInf ?_
    rintro _ ⟨σ, hσ, hγ, rfl⟩
    have hc1 := htrle σ hσ hγ
    have him := (x8_tr_psd hσ).2
    have htr : σ.trace = ((σ.trace.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rcases (x8_tr_psd hσ).1.eq_or_lt with h0 | h0
    · have : σ = 0 := (hσ.trace_eq_zero_iff).1 (by rw [htr, ← h0]; simp)
      subst this; exact hzeroComparison
    · refine le_trans ?_ (x8_D_lower D hD rho hrho σ hσ _ h0 htr)
      rw [show (0 : EReal) = ((0 : ℝ) : EReal) from rfl, EReal.coe_le_coe_iff]
      have := Real.logb_nonpos (b := 2) (by norm_num) h0.le hc1
      linarith
  refine ⟨?_, hpos, ?_, ?_, ?_⟩
  · rw [hcg, show (0 : EReal) = ((0 : ℝ) : EReal) from rfl, EReal.coe_le_coe_iff]
    exact Real.logb_nonneg (by norm_num) hg1
  · intro hprod
    have h1 := x8_prod_one hprod
    have hg : g = 1 := le_antisymm (csInf_le ⟨0, fun _ h => x8_G_nonneg h⟩ h1) hg1
    refine ⟨by rw [hcg, hg, Real.logb_one]; rfl, le_antisymm ?_ hpos⟩
    have hle : capitalGamma D rho ≤ D rho rho := sInf_le ⟨rho, hrho.1, x8_cg_le h1, rfl⟩
    refine hle.trans (le_of_eq ?_)
    exact hD.zeroValue rho hrho
  · intro h0
    rw [hcg] at h0
    have hl : Real.logb 2 g = 0 := by exact_mod_cast h0
    have hg : g = 1 := by
      by_contra hne1
      have : 0 < Real.logb 2 g := Real.logb_pos (by norm_num) (lt_of_le_of_ne hg1 (Ne.symm hne1))
      linarith
    have hγ : correlationGauge rho ≤ 1 := by rw [x8_cg_eq _ hne, ← hg_def, hg]; rfl
    exact x8_LL2 rho hrho (fun _ => rho) (fun _ => hrho.1.1) (fun _ => hγ) tendsto_const_nhds
  · intro hfaith hlsc h0
    have hseq : ∀ n : ℕ, ∃ σ : Matrix (A × B) (A × B) ℂ, (σ.PosSemidef ∧ correlationGauge σ ≤ 1) ∧
        D rho σ < ((1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
      intro n
      have : capitalGamma D rho < ((1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
        rw [h0, show (0 : EReal) = ((0 : ℝ) : EReal) from rfl]
        exact EReal.coe_lt_coe_iff.2 (by positivity)
      obtain ⟨_, ⟨σ, hσ, hγ, rfl⟩, hlt⟩ := sInf_lt_iff.1 this
      exact ⟨σ, ⟨hσ, hγ⟩, hlt⟩
    choose σ hσ hDσ using hseq
    have hK : ∀ n, σ n ∈ x8K := fun n => ⟨(hσ n).1, htrle _ (hσ n).1 (hσ n).2⟩
    haveI : FirstCountableTopology (Matrix (A × B) (A × B) ℂ) :=
      inferInstanceAs (FirstCountableTopology (A × B → A × B → ℂ))
    obtain ⟨s, hsK, φ, hφ, hlim⟩ := x8_K_compact.tendsto_subseq hK
    have hDs : D rho s ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨y, hy0, hys⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
      have hy0' : (0 : ℝ) < y := by exact_mod_cast hy0
      have hl := hlsc rho hrho ⟨s, hsK.1⟩ (y : EReal) hys
      have ht : Filter.Tendsto (fun n => (⟨σ (φ n), (hσ (φ n)).1⟩ : {s : Matrix (A × B) (A × B) ℂ // s.PosSemidef}))
          Filter.atTop (nhds ⟨s, hsK.1⟩) := tendsto_subtype_rng.2 hlim
      have ev := ht.eventually hl
      have ev2 : ∀ᶠ n : ℕ in Filter.atTop, 1 / ((n : ℝ) + 1) < y :=
        tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hy0')
      obtain ⟨n, h1, h2⟩ := (ev.and ev2).exists
      have h3 := hDσ (φ n)
      have hle : 1 / ((φ n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right (hφ.id_le n) 1)
      have : (y : EReal) < ((1 / ((n : ℝ) + 1) : ℝ) : EReal) :=
        h1.trans (h3.trans_le (EReal.coe_le_coe_iff.2 hle))
      exact absurd (EReal.coe_lt_coe_iff.1 this) (not_lt.2 h2.le)
    set c := s.trace.re with hc_def
    have him := (x8_tr_psd hsK.1).2
    have htr : s.trace = ((c : ℝ) : ℂ) := Complex.ext (by simp [c]) (by simp [him])
    have hc0 : 0 < c := by
      rcases (x8_tr_psd hsK.1).1.eq_or_lt with h | h
      · exfalso
        have : s = 0 := hsK.1.trace_eq_zero_iff.1 (by rw [htr, hc_def, ← h]; simp)
        rw [this, x8_D_zero D hD rho hrho hzeroComparison] at hDs
        exact absurd hDs (by simp)
      · exact h
    have hlow := x8_D_lower D hD rho hrho s hsK.1 c hc0 htr
    have hc1 : c = 1 := by
      have : -Real.logb 2 c ≤ 0 := by exact_mod_cast hlow.trans hDs
      have hcle : c ≤ 1 := hsK.2
      by_contra hne1
      have : Real.logb 2 c < 0 := Real.logb_neg (by norm_num) hc0 (lt_of_le_of_ne hcle hne1)
      linarith
    have hsd : QAlgorithms.IsDensityMatrix s := ⟨hsK.1, by rw [htr, hc1]; simp⟩
    have hD0 : D rho s = 0 := by
      refine le_antisymm hDs ?_
      rw [hc1, Real.logb_one, neg_zero] at hlow
      exact hlow
    have hrs : rho = s := (hfaith rho s hrho hsd).1 hD0
    rw [← hrs] at hlim
    exact x8_LL2 rho hrho (σ ∘ φ) (fun n => (hσ (φ n)).1.1) (fun n => (hσ (φ n)).2) hlim

end QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Dependency50.P18 in
theorem solution {A B : Type}
  [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]
  [Nonempty A] [Nonempty B]
  (D : Divergence) (hD : IsGeneralizedDivergence D)
    (rho : Matrix (A × B) (A × B) ℂ) (hrho : QAlgorithms.IsDensityMatrix rho)
    (hzeroComparison : 0 ≤ D rho 0) :
    0 ≤ cGamma rho ∧ 0 ≤ capitalGamma D rho ∧
    (IsProductState rho → cGamma rho = 0 ∧ capitalGamma D rho = 0) ∧
    (cGamma rho = 0 → IsProductState rho) ∧
    (DivergenceFaithful D → DivergenceLowerSemicontinuous D →
      capitalGamma D rho = 0 → IsProductState rho) :=
  x8_main D hD rho hrho hzeroComparison
