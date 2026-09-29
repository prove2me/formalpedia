-- Prove2me | solution 1 for Padic.exists_ternary_isotropic_of_sq_eq_smul_of_anticommute
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4c577492-ca1d-5b5c-877f-9d99d0842e34

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Padic_exists_ternary_isotropic_of_sq_eq_smul_of_anticommute

open Filter Topology

namespace Padic
p2m_export "Padic" "norm_int_le_pow_iff_dvd"
namespace QuaternionSplitAtEll
p2m_open "Padic"

section NormIdentity

variable {A : Type*} [AddCommGroup A] (i j : A →+ A) (u v : ℤ)

def qmap (w : Fin 4 → ℤ) : A →+ A :=
  w 0 • AddMonoidHom.id A + w 1 • i + w 2 • j + w 3 • i.comp j

def qnorm (w : Fin 4 → ℤ) : ℤ :=
  w 0 ^ 2 - u * w 1 ^ 2 - v * w 2 ^ 2 + u * v * w 3 ^ 2

def qconj (w : Fin 4 → ℤ) : Fin 4 → ℤ := ![w 0, -w 1, -w 2, -w 3]

theorem qmap_add (w w' : Fin 4 → ℤ) : qmap i j (w + w') = qmap i j w + qmap i j w' := by
  ext P
  simp only [qmap, Pi.add_apply, AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply,
    AddMonoidHom.id_apply, AddMonoidHom.comp_apply]
  module

theorem qmap_sub (w w' : Fin 4 → ℤ) : qmap i j (w - w') = qmap i j w - qmap i j w' := by
  ext P
  simp only [qmap, Pi.sub_apply, AddMonoidHom.add_apply, AddMonoidHom.sub_apply,
    AddMonoidHom.zsmul_apply, AddMonoidHom.id_apply, AddMonoidHom.comp_apply]
  module

theorem qmap_smul (c : ℤ) (w : Fin 4 → ℤ) : qmap i j (c • w) = c • qmap i j w := by
  ext P
  simp only [qmap, Pi.smul_apply, smul_eq_mul, AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply,
    AddMonoidHom.id_apply, AddMonoidHom.comp_apply]
  module

variable {i j u v}

theorem qmap_qconj_qmap (hi : ∀ a, i (i a) = u • a) (hj : ∀ a, j (j a) = v • a)
    (hij : ∀ a, i (j a) = -(j (i a))) (w : Fin 4 → ℤ) (P : A) :
    qmap i j (qconj w) (qmap i j w P) = qnorm u v w • P := by
  have hji : ∀ a, j (i a) = -(i (j a)) := fun a => by rw [hij, neg_neg]
  simp only [qmap, qconj, qnorm, AddMonoidHom.add_apply, AddMonoidHom.zsmul_apply,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply, map_add, map_zsmul, map_neg, hi, hj, hji,
    smul_neg, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  module

theorem qnorm_smul_eq_zero (hi : ∀ a, i (i a) = u • a) (hj : ∀ a, j (j a) = v • a)
    (hij : ∀ a, i (j a) = -(j (i a))) {w : Fin 4 → ℤ} {P : A} (h : qmap i j w P = 0) :
    qnorm u v w • P = 0 := by
  rw [← qmap_qconj_qmap hi hj hij w P, h, map_zero]

end NormIdentity

section Vectors

variable (ℓ : ℕ)

theorem exists_eq_pow_smul_primitive {s₀ : ℕ} {d : Fin 4 → ℤ} (hd : ∃ t, ¬ (ℓ : ℤ) ^ s₀ ∣ d t) :
    ∃ (s : ℕ) (d' : Fin 4 → ℤ), s < s₀ ∧ d = (ℓ : ℤ) ^ s • d' ∧ ∃ t, ¬ (ℓ : ℤ) ∣ d' t := by
  classical
  set Pdiv : ℕ → Prop := fun s => ∀ t, (ℓ : ℤ) ^ s ∣ d t with hP
  set s := Nat.findGreatest Pdiv s₀ with hs
  have hP0 : Pdiv 0 := fun t => by simp
  have hPs : Pdiv s := Nat.findGreatest_spec (P := Pdiv) (Nat.zero_le s₀) hP0
  have hs_le : s ≤ s₀ := Nat.findGreatest_le s₀
  have hs_lt : s < s₀ := by
    rcases hs_le.lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨t, ht⟩ := hd
      exact ht (h ▸ hPs t)
  have hnot : ¬ Pdiv (s + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self s) hs_lt
  choose d' hd' using hPs
  refine ⟨s, d', hs_lt, ?_, ?_⟩
  · funext t
    rw [Pi.smul_apply, smul_eq_mul]
    exact hd' t
  · by_contra hall
    push Not at hall
    apply hnot
    intro t
    obtain ⟨e, he⟩ := hall t
    refine ⟨e, ?_⟩
    rw [hd' t, he]
    ring

end Vectors

section Counting

variable {A : Type*} [AddCommGroup A] {i j : A →+ A} {u v : ℤ}
variable (ℓ : ℕ) [Fact ℓ.Prime]

theorem eq_of_div_eq_of_dvd_sub {M : ℕ} {a b : ℕ} (hq : a / M = b / M)
    (hdvd : (M : ℤ) ∣ (a : ℤ) - (b : ℤ)) : a = b := by
  have ha := Nat.div_add_mod a M
  have hb := Nat.div_add_mod b M
  have hmod : a % M = b % M := by
    have h1 : (b : ℤ) ≡ (a : ℤ) [ZMOD (M : ℤ)] := Int.modEq_iff_dvd.mpr hdvd
    have h2 : (b : ℤ) % (M : ℤ) = (a : ℤ) % (M : ℤ) := h1
    have h3 : ((b % M : ℕ) : ℤ) = ((a % M : ℕ) : ℤ) := by push_cast; exact h2
    exact_mod_cast h3.symm
  calc a = M * (a / M) + a % M := ha.symm
    _ = M * (b / M) + b % M := by rw [hq, hmod]
    _ = b := hb

theorem exists_primitive_pow_dvd_qnorm (hi : ∀ a, i (i a) = u • a) (hj : ∀ a, j (j a) = v • a)
    (hij : ∀ a, i (j a) = -(j (i a))) {n : ℕ} (hn : 2 ≤ n)
    (T : Finset A) (hTcard : T.card ≤ ℓ ^ (2 * n)) {P₀ : A}
    (hmemT : ∀ w : Fin 4 → ℤ, qmap i j w P₀ ∈ T)
    (hord : ∀ m : ℤ, m • P₀ = 0 → ((ℓ ^ n : ℕ) : ℤ) ∣ m) :
    ∃ d' : Fin 4 → ℤ, (∃ t, ¬ (ℓ : ℤ) ∣ d' t) ∧ (ℓ : ℤ) ^ (n / 2) ∣ qnorm u v d' := by
  classical
  have hℓ : Fact ℓ.Prime := inferInstance
  have hℓ1 : 1 < ℓ := hℓ.out.one_lt
  have hℓpos : 0 < ℓ := hℓ.out.pos
  set s₀ : ℕ := n / 2 + 1 with hs₀
  have hs₀n : s₀ ≤ n := by omega

  let box : Type := Fin 4 → Fin (ℓ ^ n)
  let toVec : box → (Fin 4 → ℤ) := fun w t => ((w t : ℕ) : ℤ)
  let f : box → T := fun w => ⟨qmap i j (toVec w) P₀, hmemT _⟩
  have hTne : Nonempty T := ⟨f fun _ => ⟨0, pow_pos hℓpos n⟩⟩
  have hcard_box : Fintype.card box = ℓ ^ (4 * n) := by
    simp [box, Fintype.card_fin, pow_mul]
    ring
  have hmul : Fintype.card T * ℓ ^ (2 * n) ≤ Fintype.card box := by
    rw [hcard_box, Fintype.card_coe]
    calc T.card * ℓ ^ (2 * n) ≤ ℓ ^ (2 * n) * ℓ ^ (2 * n) := Nat.mul_le_mul_right _ hTcard
      _ = ℓ ^ (4 * n) := by rw [← pow_add]; ring_nf
  obtain ⟨y₀, hy₀⟩ := Fintype.exists_le_card_fiber_of_mul_le_card (f := f) hmul
  set F₀ : Finset box := Finset.univ.filter fun w => f w = y₀ with hF₀
  have hF₀card : ℓ ^ (2 * n) ≤ F₀.card := hy₀
  have hF₀ne : F₀.Nonempty := by
    rw [← Finset.card_pos]
    exact lt_of_lt_of_le (pow_pos hℓpos _) hF₀card
  obtain ⟨w₀, hw₀⟩ := hF₀ne

  have key : ∃ w ∈ F₀, ∃ t, ¬ (ℓ : ℤ) ^ s₀ ∣ toVec w t - toVec w₀ t := by
    by_contra hall
    push Not at hall

    let g : box → (Fin 4 → Fin (ℓ ^ (n - s₀))) := fun w t =>
      ⟨(w t : ℕ) / ℓ ^ s₀, by
        apply Nat.div_lt_of_lt_mul
        rw [← pow_add, Nat.add_sub_cancel' hs₀n]
        exact (w t).2⟩
    have hg : Set.InjOn g F₀ := by
      intro w hw w' hw' hww'
      funext t
      apply Fin.ext
      have hq : (w t : ℕ) / ℓ ^ s₀ = (w' t : ℕ) / ℓ ^ s₀ := by
        have := congrFun hww' t
        simpa [g] using this
      have h1 := hall w hw t
      have h2 := hall w' hw' t
      have hdvd : ((ℓ ^ s₀ : ℕ) : ℤ) ∣ ((w t : ℕ) : ℤ) - ((w' t : ℕ) : ℤ) := by
        have := dvd_sub h1 h2
        push_cast at this ⊢
        simpa [toVec] using this
      exact eq_of_div_eq_of_dvd_sub hq hdvd
    have hle : F₀.card ≤ Fintype.card (Fin 4 → Fin (ℓ ^ (n - s₀))) := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card_of_injOn g (fun _ _ => Finset.mem_univ _) hg
    have hcard2 : Fintype.card (Fin 4 → Fin (ℓ ^ (n - s₀))) = ℓ ^ (4 * (n - s₀)) := by
      simp [Fintype.card_fin, pow_mul]
      ring
    rw [hcard2] at hle
    have hlt : ℓ ^ (4 * (n - s₀)) < ℓ ^ (2 * n) := Nat.pow_lt_pow_right hℓ1 (by omega)
    exact absurd (hF₀card.trans hle) (not_le.mpr hlt)
  obtain ⟨w, hw, hnd⟩ := key

  set d : Fin 4 → ℤ := toVec w - toVec w₀ with hd
  have hd0 : qmap i j d P₀ = 0 := by
    have h1 : f w = y₀ := (Finset.mem_filter.mp hw).2
    have h2 : f w₀ = y₀ := (Finset.mem_filter.mp hw₀).2
    have h3 : qmap i j (toVec w) P₀ = qmap i j (toVec w₀) P₀ := by
      have := congrArg Subtype.val (h1.trans h2.symm)
      simpa [f] using this
    rw [hd, qmap_sub, AddMonoidHom.sub_apply, h3, sub_self]

  obtain ⟨s, d', hs, hdd', hprim⟩ := exists_eq_pow_smul_primitive ℓ (d := d) (s₀ := s₀) hnd
  refine ⟨d', hprim, ?_⟩

  have h1 : qmap i j d' ((ℓ : ℤ) ^ s • P₀) = 0 := by
    rw [map_zsmul, ← AddMonoidHom.zsmul_apply, ← qmap_smul, ← hdd', hd0]
  have h2 := qnorm_smul_eq_zero hi hj hij h1
  rw [smul_smul] at h2
  have h3 := hord _ h2
  have hsn : s ≤ n := by omega
  have h4 : ((ℓ ^ n : ℕ) : ℤ) = (ℓ : ℤ) ^ (n - s) * (ℓ : ℤ) ^ s := by
    push_cast
    rw [← pow_add, Nat.sub_add_cancel hsn]
  rw [h4] at h3
  have h5 : (ℓ : ℤ) ^ (n - s) ∣ qnorm u v d' :=
    (mul_dvd_mul_iff_right (pow_ne_zero s (by exact_mod_cast hℓ.out.ne_zero))).mp h3
  exact (pow_dvd_pow (ℓ : ℤ) (by omega : n / 2 ≤ n - s)).trans h5

end Counting

section Approximate

variable {A : Type*} [AddCommGroup A] {i j : A →+ A} {u v : ℤ}
variable (ℓ : ℕ) [Fact ℓ.Prime]

theorem forall_exists_primitive_pow_dvd_qnorm
    (hA : ∀ n : ℕ, Nonempty (ZMod (ℓ ^ n) × ZMod (ℓ ^ n) ≃+ Submodule.torsionBy ℤ A ((ℓ ^ n : ℕ) : ℤ)))
    (hi : ∀ a, i (i a) = u • a) (hj : ∀ a, j (j a) = v • a) (hij : ∀ a, i (j a) = -(j (i a))) (m : ℕ) :
    ∃ d' : Fin 4 → ℤ, (∃ t, ¬ (ℓ : ℤ) ∣ d' t) ∧ (ℓ : ℤ) ^ m ∣ qnorm u v d' := by
  classical
  have hℓ : Fact ℓ.Prime := inferInstance
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = 2 * m + 2 := ⟨_, rfl⟩
  have hn2 : 2 ≤ n := by omega
  obtain ⟨e⟩ := hA n
  haveI : NeZero (ℓ ^ n) := ⟨pow_ne_zero n hℓ.out.ne_zero⟩

  set Tsub := Submodule.torsionBy ℤ A ((ℓ ^ n : ℕ) : ℤ) with hTsub
  haveI : Fintype Tsub := Fintype.ofEquiv _ e.toEquiv
  set T : Finset A := Finset.univ.map ⟨((↑) : Tsub → A), Subtype.val_injective⟩ with hT
  have hTcard : T.card ≤ ℓ ^ (2 * n) := by
    rw [hT, Finset.card_map, Finset.card_univ, ← Fintype.card_congr e.toEquiv, Fintype.card_prod,
      ZMod.card, ← pow_add, two_mul]

  set P₀ : A := ((e (1, 0) : Tsub) : A) with hP₀
  have hP₀tor : ((ℓ ^ n : ℕ) : ℤ) • P₀ = 0 := (Submodule.mem_torsionBy_iff _ _).mp (e (1, 0)).2
  have hmemT : ∀ w : Fin 4 → ℤ, qmap i j w P₀ ∈ T := by
    intro w
    rw [hT, Finset.mem_map]
    refine ⟨⟨qmap i j w P₀, ?_⟩, Finset.mem_univ _, rfl⟩
    rw [Submodule.mem_torsionBy_iff]
    change ((ℓ ^ n : ℕ) : ℤ) • qmap i j w P₀ = 0
    rw [← map_zsmul, hP₀tor, map_zero]
  have hord : ∀ c : ℤ, c • P₀ = 0 → ((ℓ ^ n : ℕ) : ℤ) ∣ c := by
    intro c hc
    have h1 : c • e (1, 0) = 0 := by
      apply Subtype.ext
      show ((c • e (1, 0) : Tsub) : A) = 0
      rw [Submodule.coe_smul]
      exact hc
    have h2 : c • ((1, 0) : ZMod (ℓ ^ n) × ZMod (ℓ ^ n)) = 0 := by
      apply e.injective
      rw [map_zsmul, h1, map_zero]
    have h3 : (c : ZMod (ℓ ^ n)) = 0 := by
      have := congrArg Prod.fst h2
      simpa using this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd c (ℓ ^ n)).mp h3
  obtain ⟨d', hprim, hdvd⟩ :=
    exists_primitive_pow_dvd_qnorm ℓ hi hj hij hn2 T hTcard hmemT hord
  refine ⟨d', hprim, (pow_dvd_pow (ℓ : ℤ) ?_).trans hdvd⟩
  omega

end Approximate

section Compactness

variable (ℓ : ℕ) [Fact ℓ.Prime] (u v : ℤ)

noncomputable def qnormPadicInt (b : Fin 4 → ℤ_[ℓ]) : ℤ_[ℓ] :=
  b 0 ^ 2 - u * b 1 ^ 2 - v * b 2 ^ 2 + u * v * b 3 ^ 2

theorem continuous_qnormPadicInt : Continuous (qnormPadicInt ℓ u v) := by
  unfold qnormPadicInt
  fun_prop

theorem qnormPadicInt_intCast (w : Fin 4 → ℤ) :
    qnormPadicInt ℓ u v (fun t => (w t : ℤ_[ℓ])) = (qnorm u v w : ℤ_[ℓ]) := by
  simp [qnormPadicInt, qnorm]

theorem exists_padicInt_zero
    (h : ∀ m : ℕ, ∃ d' : Fin 4 → ℤ, (∃ t, ¬ (ℓ : ℤ) ∣ d' t) ∧ (ℓ : ℤ) ^ m ∣ qnorm u v d') :
    ∃ b : Fin 4 → ℤ_[ℓ], (∃ t, ‖b t‖ = 1) ∧ qnormPadicInt ℓ u v b = 0 := by
  have hℓ : Fact ℓ.Prime := inferInstance
  choose d hd using h
  choose t ht using fun m => (hd m).1
  have hdvd : ∀ m, (ℓ : ℤ) ^ m ∣ qnorm u v (d m) := fun m => (hd m).2

  obtain ⟨t₀, ht₀⟩ := Finite.exists_infinite_fiber t
  have hfreq : ∃ᶠ m in atTop, t m = t₀ := by
    rw [Nat.frequently_atTop_iff_infinite]
    exact Set.infinite_coe_iff.mp ht₀

  set x : ℕ → (Fin 4 → ℤ_[ℓ]) := fun m r => (d m r : ℤ_[ℓ]) with hx
  set S : Set (Fin 4 → ℤ_[ℓ]) := {b | ‖b t₀‖ = 1} with hS
  have hSclosed : IsClosed S := isClosed_eq ((continuous_apply t₀).norm) continuous_const
  have hScomp : IsCompact S := hSclosed.isCompact
  have hxS : ∃ᶠ m in atTop, x m ∈ S := by
    refine hfreq.mono fun m hm => ?_
    show ‖(d m t₀ : ℤ_[ℓ])‖ = 1
    have h1 : ¬ ‖(d m t₀ : ℤ_[ℓ])‖ < 1 := by
      rw [PadicInt.norm_int_lt_one_iff_dvd]
      rw [← hm]
      exact ht m
    exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp h1)
  obtain ⟨b, hbS, φ, hφ, hlim⟩ := hScomp.tendsto_subseq' hxS
  refine ⟨b, ⟨t₀, hbS⟩, ?_⟩

  have hlim1 : Tendsto (fun m => qnormPadicInt ℓ u v (x (φ m))) atTop (𝓝 (qnormPadicInt ℓ u v b)) :=
    ((continuous_qnormPadicInt ℓ u v).tendsto b).comp hlim
  have hlim2 : Tendsto (fun m => qnormPadicInt ℓ u v (x (φ m))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound : ∀ m, ‖qnormPadicInt ℓ u v (x (φ m))‖ ≤ ((ℓ : ℝ)⁻¹) ^ m := by
      intro m
      rw [hx, qnormPadicInt_intCast, inv_pow, ← zpow_natCast, ← zpow_neg]
      apply PadicInt.norm_int_le_pow_iff_dvd.mpr
      have hle : m ≤ φ m := hφ.id_le m
      exact (pow_dvd_pow (ℓ : ℤ) hle).trans (by exact_mod_cast hdvd (φ m))
    have hgeom : Tendsto (fun m : ℕ => ((ℓ : ℝ)⁻¹) ^ m) atTop (𝓝 0) := by
      apply tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hℓ.out.one_lt)
    exact squeeze_zero (fun m => norm_nonneg _) hbound hgeom
  exact tendsto_nhds_unique hlim1 hlim2

end Compactness

section Algebra

variable {K : Type*} [Field K]

theorem exists_legendre_of_qnorm_zero (u v : K) {a b c d : K} (hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0))
    (h : a ^ 2 - u * b ^ 2 - v * c ^ 2 + u * v * d ^ 2 = 0) :
    ∃ z x y : K, ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - u * x ^ 2 - v * y ^ 2 = 0 := by
  by_cases hγ : c ^ 2 - u * d ^ 2 = 0
  · by_cases hcd : c = 0 ∧ d = 0
    · obtain ⟨rfl, rfl⟩ := hcd

      refine ⟨a, b, 0, ?_, by linear_combination h⟩
      rintro ⟨ha, hb, -⟩
      exact hne ⟨ha, hb, rfl, rfl⟩
    · refine ⟨c, d, 0, ?_, by linear_combination hγ⟩
      rintro ⟨hc, hd, -⟩
      exact hcd ⟨hc, hd⟩
  ·
    refine ⟨(a * c - u * b * d) / (c ^ 2 - u * d ^ 2), (b * c - a * d) / (c ^ 2 - u * d ^ 2), 1, ?_, ?_⟩
    · rintro ⟨-, -, h1⟩
      exact one_ne_zero h1
    · field_simp
      linear_combination (c ^ 2 - u * d ^ 2) * h

end Algebra

end Padic.QuaternionSplitAtEll

open Padic.QuaternionSplitAtEll in
theorem solution {A : Type*} [AddCommGroup A] (ℓ : ℕ) [Fact ℓ.Prime] (hA : ∀ n : ℕ, Nonempty (ZMod (ℓ ^ n) × ZMod (ℓ ^ n) ≃+ Submodule.torsionBy ℤ A ((ℓ ^ n : ℕ) : ℤ))) (u v : ℤ) (i j : A →+ A) (hi : ∀ a, i (i a) = u • a) (hj : ∀ a, j (j a) = v • a) (hij : ∀ a, i (j a) = -(j (i a))) : ∃ z x y : ℚ_[ℓ], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - (u : ℚ_[ℓ]) * x ^ 2 - (v : ℚ_[ℓ]) * y ^ 2 = 0 := by
  obtain ⟨b, ⟨t₀, ht₀⟩, hb⟩ := exists_padicInt_zero ℓ u v
    (forall_exists_primitive_pow_dvd_qnorm ℓ hA hi hj hij)

  have hb' : ((b 0 : ℤ_[ℓ]) : ℚ_[ℓ]) ^ 2 - (u : ℚ_[ℓ]) * ((b 1 : ℤ_[ℓ]) : ℚ_[ℓ]) ^ 2
      - (v : ℚ_[ℓ]) * ((b 2 : ℤ_[ℓ]) : ℚ_[ℓ]) ^ 2
      + (u : ℚ_[ℓ]) * (v : ℚ_[ℓ]) * ((b 3 : ℤ_[ℓ]) : ℚ_[ℓ]) ^ 2 = 0 := by
    have := congrArg ((↑) : ℤ_[ℓ] → ℚ_[ℓ]) hb
    simpa [qnormPadicInt] using this
  have hne : ¬ (((b 0 : ℤ_[ℓ]) : ℚ_[ℓ]) = 0 ∧ ((b 1 : ℤ_[ℓ]) : ℚ_[ℓ]) = 0 ∧
      ((b 2 : ℤ_[ℓ]) : ℚ_[ℓ]) = 0 ∧ ((b 3 : ℤ_[ℓ]) : ℚ_[ℓ]) = 0) := by
    intro h
    have hall : ∀ t : Fin 4, ((b t : ℤ_[ℓ]) : ℚ_[ℓ]) = 0 := by
      intro t
      fin_cases t
      exacts [h.1, h.2.1, h.2.2.1, h.2.2.2]
    have hb0 : b t₀ = 0 := Subtype.ext (by simpa using hall t₀)
    have := ht₀
    rw [hb0, norm_zero] at this
    exact zero_ne_one this
  exact exists_legendre_of_qnorm_zero (u : ℚ_[ℓ]) (v : ℚ_[ℓ]) hne hb'

end S_Padic_exists_ternary_isotropic_of_sq_eq_smul_of_anticommute
end P2MW
export P2MW.S_Padic_exists_ternary_isotropic_of_sq_eq_smul_of_anticommute (solution)
