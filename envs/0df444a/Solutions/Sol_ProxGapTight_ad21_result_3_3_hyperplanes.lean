-- Prove2me | solution 1 for ProxGapTight.ad21_result_3_3_hyperplanes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T23:55:51.632238+00:00
-- url     : https://prove2.me/submissions/029af1fc-934d-4e3c-b6cb-b13a004eb516

import Mathlib
import Theorems.Thm_ProxGapTight_adsw20_cor_2_2_7_plane

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-!
q366 blueprint: `ProxGapTight.ad21_result_3_3_hyperplanes` from the plane statement
`ProxGapTight.adsw20_cor_2_2_7_plane`. Mathematics: p2m-standalone/missions/
q366-stoc-johnson-proximity-gaps-retry/notes/PLAN.md. Development only.

Everything lives in one ambient space `Fin N → K`; points are `Lines K N`; a subspace `U` carries
the code `Code p U` spanned by indicators of hyperplanes of `U`.
-/
/-- the points of a subspace -/
noncomputable def pts (U : Submodule K (Fin N → K)) : Finset (Lines K N) := by
  classical exact Finset.univ.filter (fun ℓ => ℓ.1 ≤ U)

/-- `F_p`-valued indicator of the points of a subspace -/
noncomputable def ind (p : ℕ) (W : Submodule K (Fin N → K)) : Lines K N → ZMod p :=
  Set.indicator {ℓ : Lines K N | ℓ.1 ≤ W} (fun _ => (1 : ZMod p))

/-- `W` is a hyperplane of `U` -/
def IsHyp (W U : Submodule K (Fin N → K)) : Prop :=
  W ≤ U ∧ Module.finrank K W + 1 = Module.finrank K U

/-- the code of points and hyperplanes of `U` -/
noncomputable def Code (p : ℕ) (U : Submodule K (Fin N → K)) :
    Submodule (ZMod p) (Lines K N → ZMod p) :=
  Submodule.span (ZMod p) {f | ∃ W, IsHyp W U ∧ f = ind p W}

/-- number of points of `U` where `c` is nonzero -/
noncomputable def wt {p : ℕ} (U : Submodule K (Fin N → K)) (c : Lines K N → ZMod p) : ℕ := by
  classical exact ((pts U).filter (fun ℓ => c ℓ ≠ 0)).card

/-- restriction of `c` to the points of `T` (zero elsewhere) -/
noncomputable def res {p : ℕ} (T : Submodule K (Fin N → K)) (c : Lines K N → ZMod p) :
    Lines K N → ZMod p := by
  classical exact fun ℓ => if ℓ.1 ≤ T then c ℓ else 0

/-- the subspaces `V` with `T ≤ V ≤ U` and `dim V = dim T + 1` -/
noncomputable def ext (T U : Submodule K (Fin N → K)) : Finset (Submodule K (Fin N → K)) := by
  classical exact Finset.univ.filter (fun V => T ≤ V ∧ V ≤ U ∧
    Module.finrank K V = Module.finrank K T + 1)

/-- the hyperplanes of `U` containing `T` -/
noncomputable def hyps (T U : Submodule K (Fin N → K)) : Finset (Submodule K (Fin N → K)) := by
  classical exact Finset.univ.filter (fun V => IsHyp V U ∧ T ≤ V)

/-- at most two hyperplanes -/
def TwoComb (p : ℕ) (U : Submodule K (Fin N → K)) (c : Lines K N → ZMod p) : Prop :=
  ∃ A B : Submodule K (Fin N → K), IsHyp A U ∧ IsHyp B U ∧
    ∃ α β : ZMod p, c = α • ind p A + β • ind p B

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
/-- `θ(k) = 1 + q + … + q^{k-1}`, the number of points of a `k`-dimensional space -/
def th (q k : ℕ) : ℕ := ∑ i ∈ Finset.range k, q ^ i

/-- the leaf's weight bound `3q^{D-2} - 3q^{D-3} - 1` -/
def Wb (q D : ℕ) : ℕ := 3 * q ^ (D - 2) - 3 * q ^ (D - 3) - 1

/-- the standing hypotheses on `q = |K| = p^a` -/
def Good (p a : ℕ) (K : Type) [Fintype K] : Prop :=
  Fintype.card K = p ^ a ∧ 32 < p ^ a ∧ p ^ a ≠ 49 ∧ p ^ a ≠ 121

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace ProxGapTight.Dev.Q366.PartI
open ProxGapTight ProxGapTight.Dev.Q366
open Classical
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ### Numerics -/
lemma th_add (q a b : ℕ) : th q (a + b) = th q a + q ^ a * th q b := by
  unfold th
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]

lemma th_zero (q : ℕ) : th q 0 = 0 := by simp [th]

lemma th_one (q : ℕ) : th q 1 = 1 := by simp [th]

lemma one_le_th (q k : ℕ) (hk : 1 ≤ k) : 1 ≤ th q k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 1 + m := ⟨k - 1, by omega⟩
  rw [th_add, th_one]
  omega

lemma th_succ_sub (q t : ℕ) : th q (t + 1) - th q t = q ^ t := by
  rw [th_add, th_one]
  omega

lemma th_sub (q t m : ℕ) : th q (t + m) - th q t = q ^ t * th q m := by
  rw [th_add]
  omega

lemma card_pos' : 0 < Fintype.card K := Fintype.card_pos

lemma th_cast (p a : ℕ) [Fact p.Prime] (hG : Good p a K) (k : ℕ) (hk : 1 ≤ k) :
    ((th (Fintype.card K) k : ℕ) : ZMod p) = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = 1 + m := ⟨k - 1, by omega⟩
  have ha : a ≠ 0 := by
    rintro rfl
    have := hG.2.1
    simp at this
  have hq : ((Fintype.card K : ℕ) : ZMod p) = 0 := by
    rw [hG.1]
    push_cast
    rw [ZMod.natCast_self, zero_pow ha]
  rw [th_add, th_one]
  push_cast
  rw [hq]
  simp

/-! ### Points -/
lemma mem_pts (U : Submodule K (Fin N → K)) (ℓ : Lines K N) : ℓ ∈ pts U ↔ ℓ.1 ≤ U := by
  simp [pts]

theorem pts_card (U : Submodule K (Fin N → K)) :
    (pts U).card = th (Fintype.card K) (Module.finrank K U) := by
  let f : Projectivization K U → Lines K N := fun v =>
    ⟨v.submodule.map U.subtype, by
      rw [← v.finrank_submodule]
      exact (LinearEquiv.finrank_eq
        (Submodule.equivMapOfInjective U.subtype U.injective_subtype _).symm)⟩
  have hinj : Function.Injective f := by
    intro v w h
    apply Projectivization.submodule_injective
    have := congrArg Subtype.val h
    simp only [f] at this
    exact Submodule.map_injective_of_injective U.injective_subtype this
  haveI : Finite (Projectivization K U) := Finite.of_injective f hinj
  haveI : Fintype (Projectivization K U) := Fintype.ofFinite _
  have himg : (pts U) = Finset.univ.image f := by
    ext ℓ
    rw [mem_pts]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hle
      let H : Submodule K U := ℓ.1.comap U.subtype
      have hH : H.map U.subtype = ℓ.1 := by
        rw [Submodule.map_comap_subtype]; exact inf_eq_right.mpr hle
      have hf1 : Module.finrank K H = 1 := by
        rw [← ℓ.2, ← hH]
        exact (LinearEquiv.finrank_eq
          (Submodule.equivMapOfInjective U.subtype U.injective_subtype H))
      refine ⟨Projectivization.mk'' H hf1, ?_⟩
      apply Subtype.ext
      simp only [f, Projectivization.submodule_mk'', hH]
    · rintro ⟨v, rfl⟩
      simp only [f]
      exact Submodule.map_subtype_le U _
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have := Projectivization.card'' K U
  rw [← Nat.card_eq_fintype_card, this, Nat.card_eq_fintype_card (α := K)]
  have hc : Nat.card U = Fintype.card K ^ Module.finrank K U := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := U), Nat.card_eq_fintype_card]
  rw [hc, th, Nat.geomSum_eq (Fintype.one_lt_card)]

end ProxGapTight.Dev.Q366.PartI
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ## Part I: infrastructure -/
alias pts_card := ProxGapTight.Dev.Q366.PartI.pts_card

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace ProxGapTight.Dev.Q366.PartI
open ProxGapTight ProxGapTight.Dev.Q366
open Classical
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
lemma pts_mono {T U : Submodule K (Fin N → K)} (h : T ≤ U) : pts T ⊆ pts U := by
  intro ℓ hℓ
  rw [mem_pts] at hℓ ⊢
  exact hℓ.trans h

lemma card_pts_sdiff {T V : Submodule K (Fin N → K)} (h : T ≤ V) :
    (pts V \ pts T).card =
      th (Fintype.card K) (Module.finrank K V) - th (Fintype.card K) (Module.finrank K T) := by
  rw [Finset.card_sdiff_of_subset (pts_mono h), pts_card, pts_card]

/-! ### Geometry -/
lemma line_le_or_inf_eq_bot (P : Lines K N) (W : Submodule K (Fin N → K)) :
    P.1 ≤ W ∨ P.1 ⊓ W = ⊥ := by
  by_cases h : P.1 ≤ W
  · exact Or.inl h
  right
  have h1 : Module.finrank K (P.1 ⊓ W : Submodule K (Fin N → K)) ≤ 1 := by
    have := Submodule.finrank_mono (inf_le_left : P.1 ⊓ W ≤ P.1)
    rwa [P.2] at this
  have h2 : Module.finrank K (P.1 ⊓ W : Submodule K (Fin N → K)) ≠ 1 := by
    intro h'
    have := Submodule.eq_of_le_of_finrank_eq (inf_le_left : P.1 ⊓ W ≤ P.1) (h'.trans P.2.symm)
    exact h (this ▸ inf_le_right)
  exact Submodule.finrank_eq_zero.mp (by omega)

lemma finrank_sup_line (T : Submodule K (Fin N → K)) (P : Lines K N) (h : ¬ P.1 ≤ T) :
    Module.finrank K (T ⊔ P.1 : Submodule K (Fin N → K)) = Module.finrank K T + 1 := by
  have := Submodule.finrank_sup_add_finrank_inf_eq T P.1
  rw [inf_comm, (line_le_or_inf_eq_bot P T).resolve_left h, finrank_bot, P.2] at this
  omega

lemma hyp_inf {H U S : Submodule K (Fin N → K)} (hH : IsHyp H U) (hSU : S ≤ U)
    (hS : ¬ S ≤ H) :
    Module.finrank K (S ⊓ H : Submodule K (Fin N → K)) + 1 = Module.finrank K S := by
  have hlt : H < H ⊔ S := lt_of_le_of_ne le_sup_left
    (fun h => hS ((le_sup_right : S ≤ H ⊔ S).trans h.symm.le))
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : Module.finrank K (H ⊔ S : Submodule K (Fin N → K)) ≤ Module.finrank K U :=
    Submodule.finrank_mono (sup_le hH.1 hSU)
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq H S
  rw [inf_comm] at h3
  have := hH.2
  omega

lemma mem_ext {T U V : Submodule K (Fin N → K)} :
    V ∈ ext T U ↔ T ≤ V ∧ V ≤ U ∧ Module.finrank K V = Module.finrank K T + 1 := by
  simp [ext]

lemma mem_hyps {T U V : Submodule K (Fin N → K)} :
    V ∈ hyps T U ↔ IsHyp V U ∧ T ≤ V := by
  simp [hyps]

/-! ### Double counting -/
lemma dc {T U : Submodule K (Fin N → K)} (S : Finset (Submodule K (Fin N → K)))
    (hS : ∀ V ∈ S, T ≤ V ∧ V ≤ U) (g : Lines K N → ℕ) :
    ∑ V ∈ S, ∑ P ∈ pts V \ pts T, g P =
      ∑ P ∈ pts U \ pts T, g P * (S.filter (fun V => P.1 ≤ V)).card := by
  have : ∀ P ∈ pts U \ pts T, g P * (S.filter (fun V => P.1 ≤ V)).card =
      ∑ V ∈ S.filter (fun V => P.1 ≤ V), g P := by
    intro P _
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  rw [Finset.sum_congr rfl this]
  apply Finset.sum_comm'
  intro V P
  simp only [Finset.mem_sdiff, mem_pts, Finset.mem_filter]
  constructor
  · rintro ⟨hV, hPV, hPT⟩
    exact ⟨⟨hV, hPV⟩, hPV.trans (hS V hV).2, hPT⟩
  · rintro ⟨⟨hV, hPV⟩, _, hPT⟩
    exact ⟨hV, hPV, hPT⟩

/-- the support indicator -/
def gi {p : ℕ} (c : Lines K N → ZMod p) (ℓ : Lines K N) : ℕ := if c ℓ ≠ 0 then 1 else 0

lemma wt_eq_sum {p : ℕ} (V : Submodule K (Fin N → K)) (c : Lines K N → ZMod p) :
    wt V c = ∑ ℓ ∈ pts V, gi c ℓ := by
  unfold wt gi
  rw [Finset.card_filter]

lemma wt_split {p : ℕ} {T V : Submodule K (Fin N → K)} (h : T ≤ V) (c : Lines K N → ZMod p) :
    wt V c = wt T c + ∑ ℓ ∈ pts V \ pts T, gi c ℓ := by
  rw [wt_eq_sum, wt_eq_sum, ← Finset.sum_sdiff (pts_mono h)]
  ring

/-! ### Extensions -/
lemma ext_filter_card {T U : Submodule K (Fin N → K)} (hTU : T ≤ U) {P : Lines K N}
    (hPU : P.1 ≤ U) (hPT : ¬ P.1 ≤ T) :
    ((ext T U).filter (fun V => P.1 ≤ V)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨T ⊔ P.1, ?_⟩
  ext V
  simp only [Finset.mem_filter, mem_ext, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hTV, hVU, hV⟩, hPV⟩
    exact (Submodule.eq_of_le_of_finrank_eq (sup_le hTV hPV)
      (by rw [finrank_sup_line T P hPT, hV])).symm
  · rintro rfl
    exact ⟨⟨le_sup_left, sup_le hTU hPU, finrank_sup_line T P hPT⟩, le_sup_right⟩

theorem ext_card {T U : Submodule K (Fin N → K)} (hTU : T ≤ U) :
    (ext T U).card = th (Fintype.card K) (Module.finrank K U - Module.finrank K T) := by
  have key := dc (ext T U) (fun V hV => ⟨(mem_ext.mp hV).1, (mem_ext.mp hV).2.1⟩) (fun _ => 1)
  have hL : ∀ V ∈ ext T U, ∑ P ∈ pts V \ pts T, (fun _ => 1) P = Fintype.card K ^ Module.finrank K T := by
    intro V hV
    rw [Finset.sum_const, smul_eq_mul, mul_one, card_pts_sdiff (mem_ext.mp hV).1,
      (mem_ext.mp hV).2.2, th_succ_sub]
  have hR : ∀ P ∈ pts U \ pts T, (fun _ => 1) P * ((ext T U).filter (fun V => P.1 ≤ V)).card = 1 := by
    intro P hP
    simp only [Finset.mem_sdiff, mem_pts] at hP
    rw [ext_filter_card hTU hP.1 hP.2]
    rfl
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, mul_one, card_pts_sdiff hTU] at key
  have hle : Module.finrank K T ≤ Module.finrank K U := Submodule.finrank_mono hTU
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank K U = Module.finrank K T + m := ⟨_, (Nat.add_sub_of_le hle).symm⟩
  rw [hm, th_sub] at key
  rw [hm, Nat.add_sub_cancel_left]
  have hpos : 0 < Fintype.card K ^ Module.finrank K T := pow_pos card_pos' _
  rw [mul_comm] at key
  exact Nat.eq_of_mul_eq_mul_left hpos key

end ProxGapTight.Dev.Q366.PartI
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
alias ext_card := ProxGapTight.Dev.Q366.PartI.ext_card

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace ProxGapTight.Dev.Q366.PartI
open ProxGapTight ProxGapTight.Dev.Q366
open Classical
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
theorem ext_partition {p : ℕ} {T U : Submodule K (Fin N → K)} (hTU : T ≤ U)
    (c : Lines K N → ZMod p) :
    wt U c + (ext T U).card * wt T c = wt T c + ∑ V ∈ ext T U, wt V c := by
  have key := dc (ext T U) (fun V hV => ⟨(mem_ext.mp hV).1, (mem_ext.mp hV).2.1⟩) (gi c)
  have hR : ∀ P ∈ pts U \ pts T, gi c P * ((ext T U).filter (fun V => P.1 ≤ V)).card = gi c P := by
    intro P hP
    simp only [Finset.mem_sdiff, mem_pts] at hP
    rw [ext_filter_card hTU hP.1 hP.2, mul_one]
  rw [Finset.sum_congr rfl hR] at key
  have hV : ∀ V ∈ ext T U, wt V c = wt T c + ∑ ℓ ∈ pts V \ pts T, gi c ℓ :=
    fun V hV => wt_split (mem_ext.mp hV).1 c
  rw [Finset.sum_congr rfl hV, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, key,
    wt_split hTU c]
  ring

end ProxGapTight.Dev.Q366.PartI
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
alias ext_partition := ProxGapTight.Dev.Q366.PartI.ext_partition

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace ProxGapTight.Dev.Q366.PartI
open ProxGapTight ProxGapTight.Dev.Q366
open Classical
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ### Hyperplanes through a subspace -/
lemma hyps_filter (T U : Submodule K (Fin N → K)) (P : Lines K N) :
    (hyps T U).filter (fun V => P.1 ≤ V) = hyps (T ⊔ P.1) U := by
  ext V
  simp only [Finset.mem_filter, mem_hyps, sup_le_iff]
  tauto

lemma hyps_card_aux (m : ℕ) : ∀ T U : Submodule K (Fin N → K), T ≤ U →
    Module.finrank K U - Module.finrank K T = m →
    (hyps T U).card = th (Fintype.card K) m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro T U hTU hm
  have hle : Module.finrank K T ≤ Module.finrank K U := Submodule.finrank_mono hTU
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · interval_cases m
    · have hTeq : T = U := Submodule.eq_of_le_of_finrank_eq hTU (by omega)
      subst hTeq
      rw [th_zero, Finset.card_eq_zero]
      ext V
      simp only [mem_hyps, Finset.notMem_empty, iff_false, not_and]
      intro hV hTV
      have := Submodule.finrank_mono hTV
      have := hV.2
      omega
    · rw [th_one, Finset.card_eq_one]
      refine ⟨T, ?_⟩
      ext V
      simp only [mem_hyps, Finset.mem_singleton]
      constructor
      · rintro ⟨hV, hTV⟩
        exact (Submodule.eq_of_le_of_finrank_eq hTV (by have := hV.2; omega)).symm
      · rintro rfl
        exact ⟨⟨hTU, by omega⟩, le_rfl⟩
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
    have key := dc (hyps T U) (fun V hV => ⟨(mem_hyps.mp hV).2, (mem_hyps.mp hV).1.1⟩) (fun _ => 1)
    set q := Fintype.card K
    set t := Module.finrank K T
    have hL : ∀ V ∈ hyps T U, ∑ P ∈ pts V \ pts T, (fun _ => 1) P = q ^ t * th q (n + 1) := by
      intro V hV
      rw [Finset.sum_const, smul_eq_mul, mul_one, card_pts_sdiff (mem_hyps.mp hV).2]
      have h2 := (mem_hyps.mp hV).1.2
      have : Module.finrank K V = t + (n + 1) := by omega
      rw [this, th_sub]
    have hR : ∀ P ∈ pts U \ pts T,
        (fun _ => 1) P * ((hyps T U).filter (fun V => P.1 ≤ V)).card = th q (n + 1) := by
      intro P hP
      simp only [Finset.mem_sdiff, mem_pts] at hP
      rw [hyps_filter, one_mul]
      apply ih (n + 1) (by omega) _ _ (sup_le hTU hP.1)
      rw [finrank_sup_line T P hP.2]
      omega
    rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR, Finset.sum_const, Finset.sum_const,
      smul_eq_mul, smul_eq_mul, card_pts_sdiff hTU] at key
    have hu : Module.finrank K U = t + (n + 2) := by omega
    rw [hu, th_sub] at key
    have hpos : 0 < q ^ t * th q (n + 1) :=
      Nat.mul_pos (pow_pos card_pos' _) (one_le_th _ _ (by omega))
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [mul_comm, key]
    ring

theorem hyps_card {T U : Submodule K (Fin N → K)} (hTU : T ≤ U) :
    (hyps T U).card = th (Fintype.card K) (Module.finrank K U - Module.finrank K T) :=
  hyps_card_aux _ T U hTU rfl

end ProxGapTight.Dev.Q366.PartI
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
alias hyps_card := ProxGapTight.Dev.Q366.PartI.hyps_card

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace ProxGapTight.Dev.Q366.PartI
open ProxGapTight ProxGapTight.Dev.Q366
open Classical
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
theorem hyps_sum {p : ℕ} {T U : Submodule K (Fin N → K)} (hTU : T ≤ U)
    (hlt : Module.finrank K T < Module.finrank K U) (c : Lines K N → ZMod p) :
    ∑ V ∈ hyps T U, wt V c = (hyps T U).card * wt T c +
      th (Fintype.card K) (Module.finrank K U - Module.finrank K T - 1) * (wt U c - wt T c) := by
  have key := dc (hyps T U) (fun V hV => ⟨(mem_hyps.mp hV).2, (mem_hyps.mp hV).1.1⟩) (gi c)
  have hR : ∀ P ∈ pts U \ pts T, gi c P * ((hyps T U).filter (fun V => P.1 ≤ V)).card =
      gi c P * th (Fintype.card K) (Module.finrank K U - Module.finrank K T - 1) := by
    intro P hP
    simp only [Finset.mem_sdiff, mem_pts] at hP
    rw [hyps_filter, hyps_card (sup_le hTU hP.1), finrank_sup_line T P hP.2]
    congr 2
  rw [Finset.sum_congr rfl hR, ← Finset.sum_mul] at key
  have hV : ∀ V ∈ hyps T U, wt V c = wt T c + ∑ ℓ ∈ pts V \ pts T, gi c ℓ :=
    fun V hV => wt_split (mem_hyps.mp hV).2 c
  rw [Finset.sum_congr rfl hV, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, key,
    wt_split hTU c, Nat.add_sub_cancel_left]
  ring

/-! ### Indicators, restriction, the code -/
lemma ind_of_le {p : ℕ} {W : Submodule K (Fin N → K)} {ℓ : Lines K N} (h : ℓ.1 ≤ W) :
    ind p W ℓ = 1 := by
  simp [ind, h]

lemma ind_of_not_le {p : ℕ} {W : Submodule K (Fin N → K)} {ℓ : Lines K N} (h : ¬ ℓ.1 ≤ W) :
    ind p W ℓ = 0 := by
  simp [ind, h]

lemma res_of_le {p : ℕ} {T : Submodule K (Fin N → K)} {c : Lines K N → ZMod p} {ℓ : Lines K N}
    (h : ℓ.1 ≤ T) : res T c ℓ = c ℓ := by
  simp [res, h]

lemma res_of_not_le {p : ℕ} {T : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
    {ℓ : Lines K N} (h : ¬ ℓ.1 ≤ T) : res T c ℓ = 0 := by
  simp [res, h]

theorem code_eq_zero {p : ℕ} {U : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
    (hc : c ∈ Code p U) {ℓ : Lines K N} (h : ¬ ℓ.1 ≤ U) : c ℓ = 0 := by
  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨W, hW, rfl⟩ := hx
    exact ind_of_not_le (fun h' => h (h'.trans hW.1))
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => simp [hx]

end ProxGapTight.Dev.Q366.PartI
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
alias code_eq_zero := ProxGapTight.Dev.Q366.PartI.code_eq_zero

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace ProxGapTight.Dev.Q366.PartI
open ProxGapTight ProxGapTight.Dev.Q366
open Classical
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
theorem wt_res {p : ℕ} (T U : Submodule K (Fin N → K)) (hTU : T ≤ U)
    (c : Lines K N → ZMod p) : wt T (res U c) = wt T c := by
  rw [wt_eq_sum, wt_eq_sum]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  rw [mem_pts] at hℓ
  simp only [gi, res_of_le (hℓ.trans hTU)]

end ProxGapTight.Dev.Q366.PartI
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
alias wt_res := ProxGapTight.Dev.Q366.PartI.wt_res

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace ProxGapTight.Dev.Q366.PartI
open ProxGapTight ProxGapTight.Dev.Q366
open Classical
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
lemma sum_ind {p : ℕ} (T W : Submodule K (Fin N → K)) :
    ∑ ℓ ∈ pts T, ind p W ℓ = (((pts (T ⊓ W)).card : ℕ) : ZMod p) := by
  rw [← Finset.sum_filter_add_sum_filter_not (pts T) (fun ℓ => ℓ.1 ≤ W)]
  have h1 : ∑ ℓ ∈ (pts T).filter (fun ℓ => ℓ.1 ≤ W), ind p W ℓ =
      ∑ ℓ ∈ (pts T).filter (fun ℓ => ℓ.1 ≤ W), (1 : ZMod p) :=
    Finset.sum_congr rfl (fun ℓ hℓ => ind_of_le (Finset.mem_filter.mp hℓ).2)
  have h2 : ∑ ℓ ∈ (pts T).filter (fun ℓ => ¬ ℓ.1 ≤ W), ind p W ℓ = 0 :=
    Finset.sum_eq_zero (fun ℓ hℓ => ind_of_not_le (Finset.mem_filter.mp hℓ).2)
  have h3 : (pts T).filter (fun ℓ => ℓ.1 ≤ W) = pts (T ⊓ W) := by
    ext ℓ
    simp [mem_pts]
  rw [h1, h2, h3, Finset.sum_const, nsmul_eq_mul, mul_one, add_zero]

lemma one_le_finrank_inf {U T W : Submodule K (Fin N → K)} (hW : IsHyp W U) (hTU : T ≤ U)
    (hT : 2 ≤ Module.finrank K T) : 1 ≤ Module.finrank K (T ⊓ W : Submodule K (Fin N → K)) := by
  by_cases h : T ≤ W
  · rw [inf_eq_left.mpr h]; omega
  · have := hyp_inf hW hTU h; omega

theorem line_sum (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    {c : Lines K N → ZMod p} (hc : c ∈ Code p U) :
    ∃ σ : ZMod p, ∀ T : Submodule K (Fin N → K), T ≤ U → 2 ≤ Module.finrank K T →
      ∑ ℓ ∈ pts T, c ℓ = σ := by
  have key : ∀ T T' : Submodule K (Fin N → K), T ≤ U → 2 ≤ Module.finrank K T →
      T' ≤ U → 2 ≤ Module.finrank K T' → ∑ ℓ ∈ pts T, c ℓ = ∑ ℓ ∈ pts T', c ℓ := by
    induction hc using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨W, hW, rfl⟩ := hx
      intro T T' hTU hT hT'U hT'
      rw [sum_ind, sum_ind, pts_card, pts_card, th_cast p a hG _ (one_le_finrank_inf hW hTU hT),
        th_cast p a hG _ (one_le_finrank_inf hW hT'U hT')]
    | zero => intros; simp
    | add x y _ _ hx hy =>
      intro T T' h1 h2 h3 h4
      simp only [Pi.add_apply, Finset.sum_add_distrib, hx T T' h1 h2 h3 h4, hy T T' h1 h2 h3 h4]
    | smul r x _ hx =>
      intro T T' h1 h2 h3 h4
      simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx T T' h1 h2 h3 h4]
  by_cases h : ∃ T0 : Submodule K (Fin N → K), T0 ≤ U ∧ 2 ≤ Module.finrank K T0
  · obtain ⟨T0, h0U, h0⟩ := h
    exact ⟨_, fun T hTU hT => key T T0 hTU hT h0U h0⟩
  · exact ⟨0, fun T hTU hT => absurd ⟨T, hTU, hT⟩ h⟩

/-- `res T` as a linear map -/
noncomputable def resL (p : ℕ) (T : Submodule K (Fin N → K)) :
    (Lines K N → ZMod p) →ₗ[ZMod p] (Lines K N → ZMod p) where
  toFun := res T
  map_add' x y := by
    funext ℓ
    by_cases h : ℓ.1 ≤ T
    · simp [res_of_le h]
    · simp [res_of_not_le h]
  map_smul' r x := by
    funext ℓ
    by_cases h : ℓ.1 ≤ T
    · simp [res_of_le h]
    · simp [res_of_not_le h]

lemma sum_ind_apply {p : ℕ} (S : Finset (Submodule K (Fin N → K))) (ℓ : Lines K N) :
    (∑ H ∈ S, ind p H) ℓ = (((S.filter (fun H => ℓ.1 ≤ H)).card : ℕ) : ZMod p) := by
  rw [Finset.sum_apply, ← Finset.sum_filter_add_sum_filter_not S (fun H => ℓ.1 ≤ H)]
  have h1 : ∑ H ∈ S.filter (fun H => ℓ.1 ≤ H), ind p H ℓ =
      ∑ H ∈ S.filter (fun H => ℓ.1 ≤ H), (1 : ZMod p) :=
    Finset.sum_congr rfl (fun H hH => ind_of_le (Finset.mem_filter.mp hH).2)
  have h2 : ∑ H ∈ S.filter (fun H => ¬ ℓ.1 ≤ H), ind p H ℓ = 0 :=
    Finset.sum_eq_zero (fun H hH => ind_of_not_le (Finset.mem_filter.mp hH).2)
  rw [h1, h2, Finset.sum_const, nsmul_eq_mul, mul_one, add_zero]

/-- the all-ones word of `T` is in the code of `T` -/
lemma ind_self_mem (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {T : Submodule K (Fin N → K)}
    (hT : 2 ≤ Module.finrank K T) : ind p T ∈ Code p T := by
  have heq : ind p T = ∑ H ∈ hyps ⊥ T, ind p H := by
    funext ℓ
    rw [sum_ind_apply]
    by_cases hℓ : ℓ.1 ≤ T
    · rw [ind_of_le hℓ, hyps_filter, bot_sup_eq, hyps_card hℓ, ℓ.2,
        th_cast p a hG _ (by omega)]
    · rw [ind_of_not_le hℓ]
      have : (hyps ⊥ T).filter (fun H => ℓ.1 ≤ H) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro H hH hℓH
        exact hℓ (hℓH.trans (mem_hyps.mp hH).1.1)
      rw [this]
      simp
  rw [heq]
  exact Submodule.sum_mem _ (fun H hH => Submodule.subset_span ⟨H, (mem_hyps.mp hH).1, rfl⟩)

theorem res_mem (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U T : Submodule K (Fin N → K)}
    {c : Lines K N → ZMod p} (hc : c ∈ Code p U) (hTU : T ≤ U)
    (hT : 2 ≤ Module.finrank K T) : res T c ∈ Code p T := by
  have hle : Code p U ≤ (Code p T).comap (resL p T) := by
    rw [Code, Submodule.span_le]
    rintro f ⟨W, hW, rfl⟩
    change res T (ind p W) ∈ Code p T
    have hres : res T (ind p W) = ind p (T ⊓ W) := by
      funext ℓ
      by_cases h1 : ℓ.1 ≤ T
      · rw [res_of_le h1]
        by_cases h2 : ℓ.1 ≤ W
        · rw [ind_of_le h2, ind_of_le (le_inf h1 h2)]
        · rw [ind_of_not_le h2, ind_of_not_le (fun h => h2 (h.trans inf_le_right))]
      · rw [res_of_not_le h1, ind_of_not_le (fun h => h1 (h.trans inf_le_left))]
    rw [hres]
    by_cases h : T ≤ W
    · rw [inf_eq_left.mpr h]
      exact ind_self_mem p a hG hT
    · exact Submodule.subset_span ⟨T ⊓ W, ⟨inf_le_left, hyp_inf hW hTU h⟩, rfl⟩
  exact hle hc

end ProxGapTight.Dev.Q366.PartI
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
alias res_mem := ProxGapTight.Dev.Q366.PartI.res_mem

alias line_sum := ProxGapTight.Dev.Q366.PartI.line_sum

alias hyps_sum := ProxGapTight.Dev.Q366.PartI.hyps_sum

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace ProxGapTight.Dev.Q366.PartI
open ProxGapTight ProxGapTight.Dev.Q366
open Classical
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ### Two-hyperplane combinations -/
lemma le_wt {p : ℕ} {V : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
    {S : Finset (Lines K N)} (hS : S ⊆ pts V) (hc : ∀ ℓ ∈ S, c ℓ ≠ 0) : S.card ≤ wt V c := by
  unfold wt
  apply Finset.card_le_card
  intro ℓ hℓ
  exact Finset.mem_filter.mpr ⟨hS hℓ, hc ℓ hℓ⟩

lemma long_of {p : ℕ} {U A B : Submodule K (Fin N → K)} (hA : IsHyp A U) (hB : IsHyp B U)
    (hAB : A ≠ B) (hD : 2 ≤ Module.finrank K U) {α β : ZMod p} (hα : α ≠ 0) :
    Fintype.card K ^ (Module.finrank K U - 2) ≤ wt A (α • ind p A + β • ind p B) := by
  have hnot : ¬ A ≤ B := fun h =>
    hAB (Submodule.eq_of_le_of_finrank_eq h (by have := hA.2; have := hB.2; omega))
  have hdim := hyp_inf hB hA.1 hnot
  have hset : pts A \ pts B = pts A \ pts (A ⊓ B) := by
    ext ℓ
    simp only [Finset.mem_sdiff, mem_pts, le_inf_iff]
    tauto
  have hcard : (pts A \ pts B).card = Fintype.card K ^ (Module.finrank K U - 2) := by
    rw [hset, card_pts_sdiff inf_le_left]
    have e1 : Module.finrank K A = (Module.finrank K U - 2) + 1 := by have := hA.2; omega
    have e2 : Module.finrank K (A ⊓ B : Submodule K (Fin N → K)) = Module.finrank K U - 2 := by
      have := hA.2; omega
    rw [e1, e2, th_succ_sub]
  rw [← hcard]
  apply le_wt Finset.sdiff_subset
  intro ℓ hℓ
  simp only [Finset.mem_sdiff, mem_pts] at hℓ
  simp [ind_of_le hℓ.1, ind_of_not_le hℓ.2, hα]

theorem twoComb_long {p : ℕ} {U : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
    (h : TwoComb p U c) (hD : 2 ≤ Module.finrank K U) {X : Lines K N} (hX : X.1 ≤ U)
    (hcX : c X ≠ 0) :
    ∃ L, IsHyp L U ∧ X.1 ≤ L ∧ Fintype.card K ^ (Module.finrank K U - 2) ≤ wt L c := by
  obtain ⟨A, B, hA, hB, α, β, rfl⟩ := h
  by_cases hAB : A = B
  · subst hAB
    have hXA : X.1 ≤ A := by
      by_contra hn
      apply hcX
      simp [ind_of_not_le hn]
    refine ⟨A, hA, hXA, ?_⟩
    have hs : α + β ≠ 0 := by
      intro h0
      apply hcX
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ind_of_le hXA]
      rw [← add_mul, h0, zero_mul]
    have hw : (pts A).card ≤ wt A (α • ind p A + β • ind p A) := by
      apply le_wt (subset_refl _)
      intro ℓ hℓ
      rw [mem_pts] at hℓ
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ind_of_le hℓ]
      rw [← add_mul, mul_one]
      exact hs
    refine le_trans ?_ hw
    rw [pts_card]
    have e1 : Module.finrank K A = (Module.finrank K U - 2) + 1 := by have := hA.2; omega
    rw [e1, th_add, th_one]
    omega
  · by_cases h1 : X.1 ≤ A ∧ α ≠ 0
    · exact ⟨A, hA, h1.1, long_of hA hB hAB hD h1.2⟩
    by_cases h2 : X.1 ≤ B ∧ β ≠ 0
    · refine ⟨B, hB, h2.1, ?_⟩
      rw [add_comm]
      exact long_of hB hA (Ne.symm hAB) hD h2.2
    exfalso
    apply hcX
    have t1 : α * ind p A X = 0 := by
      by_cases hX : X.1 ≤ A
      · rw [show α = 0 by by_contra h; exact h1 ⟨hX, h⟩, zero_mul]
      · rw [ind_of_not_le hX, mul_zero]
    have t2 : β * ind p B X = 0 := by
      by_cases hX : X.1 ≤ B
      · rw [show β = 0 by by_contra h; exact h2 ⟨hX, h⟩, zero_mul]
      · rw [ind_of_not_le hX, mul_zero]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, t1, t2, add_zero]

end ProxGapTight.Dev.Q366.PartI
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
alias twoComb_long := ProxGapTight.Dev.Q366.PartI.twoComb_long

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace ProxGapTight.Dev.Q366.PartP
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ## Basic API -/
theorem mem_pts {U : Submodule K (Fin N → K)} {ℓ : Lines K N} : ℓ ∈ pts U ↔ ℓ.1 ≤ U := by
  unfold pts; simp

theorem ind_le {p : ℕ} {W : Submodule K (Fin N → K)} {ℓ : Lines K N} (h : ℓ.1 ≤ W) :
    ind p W ℓ = 1 := by
  classical
  unfold ind; rw [Set.indicator_apply]; simp [h]

theorem ind_nle {p : ℕ} {W : Submodule K (Fin N → K)} {ℓ : Lines K N} (h : ¬ ℓ.1 ≤ W) :
    ind p W ℓ = 0 := by
  classical
  unfold ind; rw [Set.indicator_apply]; simp [h]

theorem fr_mono {T U : Submodule K (Fin N → K)} (h : T ≤ U) :
    Module.finrank K T ≤ Module.finrank K U := Submodule.finrank_mono h

theorem eq_of_fr {T U : Submodule K (Fin N → K)} (h : T ≤ U)
    (h' : Module.finrank K U ≤ Module.finrank K T) : T = U :=
  Submodule.eq_of_le_of_finrank_le h h'

theorem line_eq_of_le {Y X : Lines K N} (h : Y.1 ≤ X.1) : Y = X :=
  Subtype.ext (eq_of_fr h (by rw [Y.2, X.2]))

/-! ## Transport of the published plane statement -/
/-- hyperplanes of `K^3` as in the published statement -/
abbrev HypT (K : Type) [Field K] : Type :=
  {H : Submodule K (Fin 3 → K) // Module.finrank K H + 1 = 3}

/-- indicator of a hyperplane of `K^3` -/
noncomputable abbrev indT (p : ℕ) (H : HypT K) : Lines K 3 → ZMod p :=
  Set.indicator {ℓ : Lines K 3 | ℓ.1 ≤ H.1} (fun _ => (1 : ZMod p))

end ProxGapTight.Dev.Q366.PartP
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace ProxGapTight.Dev.Q366.PartP
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
variable {g : (Fin 3 → K) →ₗ[K] (Fin N → K)}
theorem fr_map (hg : Function.Injective g) (W : Submodule K (Fin 3 → K)) :
    Module.finrank K (W.map g) = Module.finrank K W :=
  (Submodule.equivMapOfInjective g hg W).finrank_eq.symm

/-- the point of `K^N` corresponding to a point of `K^3` -/
noncomputable def psi (hg : Function.Injective g) (ℓ : Lines K 3) : Lines K N :=
  ⟨ℓ.1.map g, by rw [fr_map hg]; exact ℓ.2⟩

theorem psi_le (hg : Function.Injective g) (ℓ : Lines K 3) (W : Submodule K (Fin N → K)) :
    (psi hg ℓ).1 ≤ W ↔ ℓ.1 ≤ W.comap g := Submodule.map_le_iff_le_comap

theorem psi_le_map (hg : Function.Injective g) (ℓ : Lines K 3) (W : Submodule K (Fin 3 → K)) :
    (psi hg ℓ).1 ≤ W.map g ↔ ℓ.1 ≤ W := Submodule.map_le_map_iff_of_injective hg _ _

theorem psi_inj (hg : Function.Injective g) : Function.Injective (psi hg) := by
  intro x y h
  exact Subtype.ext (Submodule.map_injective_of_injective hg (congrArg Subtype.val h))

theorem fr_comap (hg : Function.Injective g) {U : Submodule K (Fin N → K)} (hr : LinearMap.range g = U)
    {W : Submodule K (Fin N → K)} (hW : W ≤ U) :
    Module.finrank K (W.comap g) = Module.finrank K W := by
  have : (W.comap g).map g = W := Submodule.map_comap_eq_of_le (hr ▸ hW)
  rw [← fr_map hg, this]

theorem psi_surj (hg : Function.Injective g) {U : Submodule K (Fin N → K)} (hr : LinearMap.range g = U)
    (x : Lines K N) (hx : x.1 ≤ U) : ∃ ℓ, psi hg ℓ = x := by
  refine ⟨⟨x.1.comap g, by rw [fr_comap hg hr hx]; exact x.2⟩, Subtype.ext ?_⟩
  exact Submodule.map_comap_eq_of_le (hr ▸ hx)

theorem map_le_U {U : Submodule K (Fin N → K)} (hr : LinearMap.range g = U)
    (W : Submodule K (Fin 3 → K)) : W.map g ≤ U := by
  rw [← hr]; exact LinearMap.map_le_range

theorem hypT_map (hg : Function.Injective g) {U : Submodule K (Fin N → K)}
    (hr : LinearMap.range g = U) (hU : Module.finrank K U = 3) (H : HypT K) :
    IsHyp (H.1.map g) U := ⟨map_le_U hr _, by rw [fr_map hg, hU]; exact H.2⟩

theorem ind_psi {p : ℕ} (hg : Function.Injective g) (H : HypT K) (ℓ : Lines K 3) :
    ind p (H.1.map g) (psi hg ℓ) = indT p H ℓ := by
  classical
  by_cases h : ℓ.1 ≤ H.1
  · rw [ind_le ((psi_le_map hg ℓ H.1).mpr h)]
    simp [indT, Set.indicator_apply, h]
  · rw [ind_nle (fun h' => h ((psi_le_map hg ℓ H.1).mp h'))]
    simp [indT, Set.indicator_apply, h]

theorem mem_span_T (p : ℕ) (hg : Function.Injective g) {U : Submodule K (Fin N → K)}
    (hr : LinearMap.range g = U) (hU : Module.finrank K U = 3) {c : Lines K N → ZMod p}
    (hc : c ∈ Code p U) :
    (fun ℓ => c (psi hg ℓ)) ∈ Submodule.span (ZMod p) (Set.range (indT p)) := by
  have h1 := Submodule.mem_map_of_mem (f := LinearMap.funLeft (ZMod p) (ZMod p) (psi hg)) hc
  rw [Code, Submodule.map_span] at h1
  refine Submodule.span_mono ?_ h1
  rintro f ⟨f0, ⟨W, hW, rfl⟩, rfl⟩
  have hfr : Module.finrank K (W.comap g) + 1 = 3 := by
    rw [fr_comap hg hr hW.1, ← hU]; exact hW.2
  refine ⟨⟨W.comap g, hfr⟩, ?_⟩
  funext ℓ
  classical
  simp only [LinearMap.funLeft_apply, indT]
  by_cases h : ℓ.1 ≤ W.comap g
  · rw [ind_le ((psi_le hg ℓ W).mpr h)]; simp [Set.indicator_apply, h]
  · rw [ind_nle (fun h' => h ((psi_le hg ℓ W).mp h'))]; simp [Set.indicator_apply, h]

theorem hamming_eq (p : ℕ) (hg : Function.Injective g) {U : Submodule K (Fin N → K)}
    (hr : LinearMap.range g = U) (c : Lines K N → ZMod p) :
    hammingNorm (fun ℓ => c (psi hg ℓ)) = wt U c := by
  classical
  unfold hammingNorm wt
  rw [← Finset.card_image_of_injective _ (psi_inj hg)]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, mem_pts]
  constructor
  · rintro ⟨ℓ, hℓ, rfl⟩
    exact ⟨(psi_le hg ℓ U).mpr (by rw [← hr]; intro v hv; exact ⟨v, rfl⟩), hℓ⟩
  · rintro ⟨hx, hcx⟩
    obtain ⟨ℓ, rfl⟩ := psi_surj hg hr x hx
    exact ⟨ℓ, hcx, rfl⟩

theorem exists_g (U : Submodule K (Fin N → K)) (hU : Module.finrank K U = 3) :
    ∃ g : (Fin 3 → K) →ₗ[K] (Fin N → K), Function.Injective g ∧ LinearMap.range g = U := by
  let e : U ≃ₗ[K] (Fin 3 → K) := LinearEquiv.ofFinrankEq U (Fin 3 → K)
    (by rw [hU, Module.finrank_fin_fun])
  refine ⟨U.subtype ∘ₗ e.symm.toLinearMap, ?_, ?_⟩
  · exact Subtype.val_injective.comp e.symm.injective
  · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]

theorem ext_U {p : ℕ} (hg : Function.Injective g) {U : Submodule K (Fin N → K)}
    (hr : LinearMap.range g = U) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (F : Lines K N → ZMod p) (hF : ∀ x : Lines K N, ¬ x.1 ≤ U → F x = 0)
    (h : ∀ ℓ, c (psi hg ℓ) = F (psi hg ℓ)) : c = F := by
  funext x
  by_cases hx : x.1 ≤ U
  · obtain ⟨ℓ, rfl⟩ := psi_surj hg hr x hx
    exact h ℓ
  · rw [code_eq_zero hc hx, hF x hx]

/-- three-hyperplane combinations -/
def Tri3 (p : ℕ) (U : Submodule K (Fin N → K)) (c : Lines K N → ZMod p) : Prop :=
  ∃ A1 A2 A3 : Submodule K (Fin N → K), IsHyp A1 U ∧ IsHyp A2 U ∧ IsHyp A3 U ∧
    ∃ α1 α2 α3 : ZMod p, c = α1 • ind p A1 + α2 • ind p A2 + α3 • ind p A3

/-- the odd type -/
def OddT (p : ℕ) (U : Submodule K (Fin N → K)) (c : Lines K N → ZMod p) : Prop :=
  ∃ S : Lines K N, ∃ H1 H2 H3 : Submodule K (Fin N → K), IsHyp H1 U ∧ IsHyp H2 U ∧ IsHyp H3 U ∧
    S.1 ≤ H1 ∧ S.1 ≤ H2 ∧ S.1 ≤ H3 ∧ H1 ≠ H2 ∧ H1 ≠ H3 ∧ H2 ≠ H3 ∧
    (∀ x : Lines K N, c x ≠ 0 → x.1 ≤ H1 ∨ x.1 ≤ H2 ∨ x.1 ≤ H3) ∧
    ∀ H, (H = H1 ∨ H = H2 ∨ H = H3) → ∀ x y : Lines K N, x.1 ≤ H → y.1 ≤ H → x ≠ S → y ≠ S →
      c x = c y → x = y

theorem plane_I (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hU : Module.finrank K U = 3) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (hw : wt U c ≤ 3 * Fintype.card K - 4) : TwoComb p U c := by
  obtain ⟨hK, hQ, h49, h121⟩ := hG
  obtain ⟨g, hg, hr⟩ := exists_g U hU
  have hv := mem_span_T p hg hr hU hc
  have pub := (adsw20_cor_2_2_7_plane p a hQ h49 h121 K hK _ hv).1
    (by rw [hamming_eq p hg hr c, ← hK]; exact hw)
  obtain ⟨H, H', α, β, heq⟩ := pub
  refine ⟨H.1.map g, H'.1.map g, hypT_map hg hr hU H, hypT_map hg hr hU H', α, β, ?_⟩
  refine ext_U hg hr hc _ ?_ ?_
  · intro x hx
    have h1 : ¬ x.1 ≤ H.1.map g := fun h => hx (h.trans (map_le_U hr _))
    have h2 : ¬ x.1 ≤ H'.1.map g := fun h => hx (h.trans (map_le_U hr _))
    simp [ind_nle h1, ind_nle h2]
  · intro ℓ
    have := congrFun heq ℓ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [ind_psi, ind_psi]; exact this

theorem plane_II (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hU : Module.finrank K U = 3) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (hw : wt U c ≤ 4 * Fintype.card K - 22) : Tri3 p U c ∨ (a = 1 ∧ OddT p U c) := by
  obtain ⟨hK, hQ, h49, h121⟩ := hG
  obtain ⟨g, hg, hr⟩ := exists_g U hU
  have hv := mem_span_T p hg hr hU hc
  have pub := (adsw20_cor_2_2_7_plane p a hQ h49 h121 K hK _ hv).2
    (by rw [hamming_eq p hg hr c, ← hK]; exact hw)
  rcases pub with ⟨H1, H2, H3, α, β, γ, heq⟩ | ⟨ha, S, H1, H2, H3, hS1, hS2, hS3, h12, h13, h23,
    hsupp, hinj⟩
  · left
    refine ⟨H1.1.map g, H2.1.map g, H3.1.map g, hypT_map hg hr hU H1, hypT_map hg hr hU H2,
      hypT_map hg hr hU H3, α, β, γ, ?_⟩
    refine ext_U hg hr hc _ ?_ ?_
    · intro x hx
      have h1 : ¬ x.1 ≤ H1.1.map g := fun h => hx (h.trans (map_le_U hr _))
      have h2 : ¬ x.1 ≤ H2.1.map g := fun h => hx (h.trans (map_le_U hr _))
      have h3 : ¬ x.1 ≤ H3.1.map g := fun h => hx (h.trans (map_le_U hr _))
      simp [ind_nle h1, ind_nle h2, ind_nle h3]
    · intro ℓ
      have := congrFun heq ℓ
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
      rw [ind_psi, ind_psi, ind_psi]; exact this
  · right
    refine ⟨ha, psi hg S, H1.1.map g, H2.1.map g, H3.1.map g, hypT_map hg hr hU H1,
      hypT_map hg hr hU H2, hypT_map hg hr hU H3, (psi_le_map hg S _).mpr hS1,
      (psi_le_map hg S _).mpr hS2, (psi_le_map hg S _).mpr hS3, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun h => h12 (Subtype.ext (Submodule.map_injective_of_injective hg h))
    · exact fun h => h13 (Subtype.ext (Submodule.map_injective_of_injective hg h))
    · exact fun h => h23 (Subtype.ext (Submodule.map_injective_of_injective hg h))
    · intro x hx
      have hxU : x.1 ≤ U := by
        by_contra h; exact hx (code_eq_zero hc h)
      obtain ⟨ℓ, rfl⟩ := psi_surj hg hr x hxU
      rcases hsupp ℓ hx with h | h | h
      · exact Or.inl ((psi_le_map hg ℓ _).mpr h)
      · exact Or.inr (Or.inl ((psi_le_map hg ℓ _).mpr h))
      · exact Or.inr (Or.inr ((psi_le_map hg ℓ _).mpr h))
    · intro H hH x y hx hy hxS hyS hxy
      have hHU : H ≤ U := by
        rcases hH with rfl | rfl | rfl <;> exact map_le_U hr _
      obtain ⟨ℓ, rfl⟩ := psi_surj hg hr x (hx.trans hHU)
      obtain ⟨ℓ', rfl⟩ := psi_surj hg hr y (hy.trans hHU)
      have hne : ℓ ≠ S := fun h => hxS (h ▸ rfl)
      have hne' : ℓ' ≠ S := fun h => hyS (h ▸ rfl)
      rcases hH with rfl | rfl | rfl
      · rw [hinj H1 (by simp) ℓ ℓ' ((psi_le_map hg ℓ _).mp hx) ((psi_le_map hg ℓ' _).mp hy)
          hne hne' hxy]
      · rw [hinj H2 (by simp) ℓ ℓ' ((psi_le_map hg ℓ _).mp hx) ((psi_le_map hg ℓ' _).mp hy)
          hne hne' hxy]
      · rw [hinj H3 (by simp) ℓ ℓ' ((psi_le_map hg ℓ _).mp hx) ((psi_le_map hg ℓ' _).mp hy)
          hne hne' hxy]

end ProxGapTight.Dev.Q366.PartP
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace ProxGapTight.Dev.Q366.PartP
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ## Plane geometry and counting -/
theorem th_two' (q : ℕ) : th q 2 = q + 1 := by simp [th, Finset.sum_range_succ]; ring

theorem th_three' (q : ℕ) : th q 3 = q * q + q + 1 := by
  simp [th, Finset.sum_range_succ]; ring

theorem card_line {L : Submodule K (Fin N → K)} (hL : Module.finrank K L = 2) :
    (pts L).card = Fintype.card K + 1 := by rw [pts_card, hL, th_two']

theorem card_plane {U : Submodule K (Fin N → K)} (hU : Module.finrank K U = 3) :
    (pts U).card = Fintype.card K * Fintype.card K + Fintype.card K + 1 := by
  rw [pts_card, hU, th_three']

theorem q_ge (p a : ℕ) (hG : Good p a K) : 33 ≤ Fintype.card K := by
  obtain ⟨hK, h32, -, -⟩ := hG; omega

theorem join_fr {x y : Lines K N} (hxy : x ≠ y) : Module.finrank K ↥(x.1 ⊔ y.1) = 2 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq x.1 y.1
  have h0 : Module.finrank K ↥(x.1 ⊓ y.1) = 0 := by
    have h2 : Module.finrank K ↥(x.1 ⊓ y.1) ≤ 1 := by
      have := fr_mono (inf_le_left : x.1 ⊓ y.1 ≤ x.1); rw [x.2] at this; exact this
    by_contra h0
    have e := eq_of_fr (inf_le_left : x.1 ⊓ y.1 ≤ x.1) (by rw [x.2]; omega)
    apply hxy
    apply line_eq_of_le
    rw [← e]; exact inf_le_right
  rw [h0, x.2, y.2] at h1; omega

theorem join_eq {x y : Lines K N} (hxy : x ≠ y) {L : Submodule K (Fin N → K)}
    (hL : Module.finrank K L = 2) (hx : x.1 ≤ L) (hy : y.1 ≤ L) : x.1 ⊔ y.1 = L :=
  eq_of_fr (sup_le hx hy) (by rw [hL, join_fr hxy])

theorem uniq {x y : Lines K N} (hxy : x ≠ y) {L M : Submodule K (Fin N → K)}
    (hL : Module.finrank K L = 2) (hM : Module.finrank K M = 2) (hxL : x.1 ≤ L) (hyL : y.1 ≤ L)
    (hxM : x.1 ≤ M) (hyM : y.1 ≤ M) : L = M := by
  rw [← join_eq hxy hL hxL hyL, join_eq hxy hM hxM hyM]

/-- two distinct lines share at most one point -/
theorem eq_pt {x y : Lines K N} {L M : Submodule K (Fin N → K)}
    (hL : Module.finrank K L = 2) (hM : Module.finrank K M = 2) (hLM : L ≠ M) (hxL : x.1 ≤ L)
    (hxM : x.1 ≤ M) (hyL : y.1 ≤ L) (hyM : y.1 ≤ M) : x = y := by
  by_contra h; exact hLM (uniq h hL hM hxL hyL hxM hyM)

theorem exists_pt {W : Submodule K (Fin N → K)} (h : W ≠ ⊥) : ∃ x : Lines K N, x.1 ≤ W := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  exact ⟨⟨K ∙ v, finrank_span_singleton hv0⟩, (Submodule.span_singleton_le_iff_mem v W).mpr hv⟩

/-- two lines of a plane meet -/
theorem meet {U L M : Submodule K (Fin N → K)} (hU : Module.finrank K U = 3) (hLU : L ≤ U)
    (hMU : M ≤ U) (hL : Module.finrank K L = 2) (hM : Module.finrank K M = 2) :
    ∃ x : Lines K N, x.1 ≤ L ∧ x.1 ≤ M := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq L M
  have h2 := fr_mono (sup_le hLU hMU)
  have hne : L ⊓ M ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at h1; omega
  obtain ⟨x, hx⟩ := exists_pt hne
  exact ⟨x, hx.trans inf_le_left, hx.trans inf_le_right⟩

/-- the support of `c` in `U` -/
noncomputable def supp {p : ℕ} (U : Submodule K (Fin N → K)) (c : Lines K N → ZMod p) :
    Finset (Lines K N) := by
  classical exact (pts U).filter (fun ℓ => c ℓ ≠ 0)

theorem wt_eq {p : ℕ} (U : Submodule K (Fin N → K)) (c : Lines K N → ZMod p) :
    wt U c = (supp U c).card := rfl

theorem mem_supp {p : ℕ} {U : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
    {ℓ : Lines K N} : ℓ ∈ supp U c ↔ ℓ.1 ≤ U ∧ c ℓ ≠ 0 := by
  unfold supp; simp [mem_pts]

theorem card_cover {L : Submodule K (Fin N → K)} (hL : Module.finrank K L = 2)
    (F : Finset (Submodule K (Fin N → K)))
    (hF : ∀ M ∈ F, Module.finrank K M = 2 ∧ M ≠ L) (X : Finset (Lines K N))
    (hX : ∀ x ∈ X, x.1 ≤ L ∧ ∃ M ∈ F, x.1 ≤ M) : X.card ≤ F.card := by
  refine Finset.card_le_card_of_forall_subsingleton (fun x M => x.1 ≤ M) (fun x hx => ?_)
    (fun M hM => ?_)
  · obtain ⟨_, M, hM, h⟩ := hX x hx; exact ⟨M, hM, h⟩
  · intro x hx y hy
    by_contra hxy
    exact (hF M hM).2 (uniq hxy (hF M hM).1 hL hx.2 hy.2 (hX x hx.1).1 (hX y hy.1).1)

theorem wt_le_cover {p : ℕ} {c : Lines K N → ZMod p} {L : Submodule K (Fin N → K)}
    (hL : Module.finrank K L = 2) (F : Finset (Submodule K (Fin N → K)))
    (hF : ∀ M ∈ F, Module.finrank K M = 2 ∧ M ≠ L)
    (h : ∀ x : Lines K N, x.1 ≤ L → c x ≠ 0 → ∃ M ∈ F, x.1 ≤ M) : wt L c ≤ F.card := by
  rw [wt_eq]
  refine card_cover hL F hF _ (fun x hx => ?_)
  rw [mem_supp] at hx; exact ⟨hx.1, h x hx.1 hx.2⟩

theorem wt_ge_cover {p : ℕ} {c : Lines K N → ZMod p} {L : Submodule K (Fin N → K)}
    (hL : Module.finrank K L = 2) (F : Finset (Submodule K (Fin N → K)))
    (hF : ∀ M ∈ F, Module.finrank K M = 2 ∧ M ≠ L)
    (h : ∀ x : Lines K N, x.1 ≤ L → (∀ M ∈ F, ¬ x.1 ≤ M) → c x ≠ 0) :
    Fintype.card K + 1 ≤ wt L c + F.card := by
  classical
  have hcov : ∀ x ∈ (pts L).filter (fun x => c x = 0), x.1 ≤ L ∧ ∃ M ∈ F, x.1 ≤ M := by
    intro x hx
    rw [Finset.mem_filter, mem_pts] at hx
    refine ⟨hx.1, ?_⟩
    by_contra hno; push Not at hno
    exact h x hx.1 hno hx.2
  have hZ := card_cover hL F hF _ hcov
  have hsub : pts L ⊆ supp L c ∪ (pts L).filter (fun x => c x = 0) := by
    intro x hx; by_cases hc : c x = 0
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hc⟩)
    · exact Finset.mem_union_left _ (mem_supp.mpr ⟨mem_pts.mp hx, hc⟩)
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [card_line hL] at this; rw [wt_eq]; omega

/-! ## Configurations of three lines -/
/-- three lines carrying the support, each heavy, with few bad points -/
structure Cfg (p : ℕ) (U : Submodule K (Fin N → K)) (c : Lines K N → ZMod p)
    (F : Finset (Submodule K (Fin N → K))) : Prop where
  card : F.card = 3
  line : ∀ M ∈ F, M ≤ U ∧ Module.finrank K M = 2
  supp : ∀ x : Lines K N, c x ≠ 0 → ∃ M ∈ F, x.1 ≤ M
  heavy : ∀ M ∈ F, Fintype.card K - 1 ≤ wt M c
  bad : ∃ B : Finset (Lines K N), B.card ≤ 6 ∧ ∀ x : Lines K N, x.1 ≤ U →
    ((∃ M ∈ F, ∃ M' ∈ F, M ≠ M' ∧ x.1 ≤ M ∧ x.1 ≤ M') ∨ ((∃ M ∈ F, x.1 ≤ M) ∧ c x = 0)) →
      x ∈ B

end ProxGapTight.Dev.Q366.PartP
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace ProxGapTight.Dev.Q366.PartP
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
variable {p : ℕ} {U : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
  {F : Finset (Submodule K (Fin N → K))}
theorem cfg_off (hC : Cfg p U c F) {L : Submodule K (Fin N → K)} (hL : Module.finrank K L = 2)
    (hLF : L ∉ F) : wt L c ≤ 3 := by
  have := wt_le_cover hL F (fun M hM => ⟨(hC.line M hM).2, fun h => hLF (h ▸ hM)⟩)
    (fun x _ hx => hC.supp x hx)
  rw [hC.card] at this; exact this

theorem cfg_lines (hC : Cfg p U c F) {L : Submodule K (Fin N → K)}
    (hL : Module.finrank K L = 2) : wt L c ≤ 3 ∨ Fintype.card K - 1 ≤ wt L c := by
  by_cases hLF : L ∈ F
  · exact Or.inr (hC.heavy L hLF)
  · exact Or.inl (cfg_off hC hL hLF)

theorem cfg_sec_notin (hC : Cfg p U c F) (hq : 33 ≤ Fintype.card K) {t : Submodule K (Fin N → K)}
    (h3 : wt t c = 3) : t ∉ F := fun h => by have := hC.heavy t h; omega

theorem cfg_meet (hC : Cfg p U c F) (hq : 33 ≤ Fintype.card K) {t : Submodule K (Fin N → K)}
    (ht : Module.finrank K t = 2) (h3 : wt t c = 3) {M : Submodule K (Fin N → K)} (hM : M ∈ F) :
    ∃ X : Lines K N, X.1 ≤ M ∧ X.1 ≤ t ∧ c X ≠ 0 := by
  classical
  by_contra hno; push Not at hno
  have htF := cfg_sec_notin hC hq h3
  have := wt_le_cover ht (F.erase M) (fun M' hM' => ⟨(hC.line M' (Finset.mem_of_mem_erase hM')).2,
    fun h => htF (h ▸ Finset.mem_of_mem_erase hM')⟩) (fun x hxt hx => by
      obtain ⟨M', hM', hxM'⟩ := hC.supp x hx
      refine ⟨M', Finset.mem_erase.mpr ⟨?_, hM'⟩, hxM'⟩
      rintro rfl; exact hx (hno x hxM' hxt))
  rw [Finset.card_erase_of_mem hM, hC.card] at this; omega

/-- a 3-secant through any point off the configuration, other than a given line -/
theorem cfg_three (hC : Cfg p U c F) (hU : Module.finrank K U = 3) (hq : 33 ≤ Fintype.card K)
    {H : Lines K N} (hHU : H.1 ≤ U) (hHF : ∀ M ∈ F, ¬ H.1 ≤ M) (t : Submodule K (Fin N → K)) :
    ∃ t' : Submodule K (Fin N → K), t' ≤ U ∧ Module.finrank K t' = 2 ∧ H.1 ≤ t' ∧ t' ≠ t ∧
      wt t' c = 3 := by
  classical
  obtain ⟨B, hB, hBad⟩ := hC.bad
  have hcard : (ext H.1 U).card = Fintype.card K + 1 := by
    rw [ext_card hHU, hU, H.2]; exact th_two' _
  have hbad : (insert t (B.image (fun b => H.1 ⊔ b.1))).card ≤ 7 := by
    have := Finset.card_image_le (s := B) (f := fun b => H.1 ⊔ b.1)
    have := Finset.card_insert_le t (B.image (fun b => H.1 ⊔ b.1))
    omega
  obtain ⟨t', ht'E, ht'bad⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := insert t (B.image (fun b => H.1 ⊔ b.1))) (t := ext H.1 U) (by omega)
  unfold ext at ht'E
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht'E
  obtain ⟨hHt, ht'U, hfr⟩ := ht'E
  have ht2 : Module.finrank K t' = 2 := by rw [hfr, H.2]
  have ht'ne : t' ≠ t := fun h => ht'bad (h ▸ Finset.mem_insert_self _ _)
  have hnotB : ∀ x : Lines K N, x.1 ≤ t' → (∃ M ∈ F, x.1 ≤ M) → x ∉ B := by
    rintro x hxt ⟨M, hM, hxM⟩ hxB
    have hHx : H ≠ x := fun h => hHF M hM (h ▸ hxM)
    have e : H.1 ⊔ x.1 = t' := join_eq hHx ht2 hHt hxt
    exact ht'bad (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hxB, e⟩))
  have ht'F : t' ∉ F := fun h => hHF t' h hHt
  refine ⟨t', ht'U, ht2, hHt, ht'ne, le_antisymm (cfg_off hC ht2 ht'F) ?_⟩
  rw [wt_eq, ← hC.card]
  refine Finset.card_le_card_of_forall_subsingleton (fun M x => x.1 ≤ M) (fun M hM => ?_)
    (fun x hx => ?_)
  · obtain ⟨X, hXt, hXM⟩ := meet hU ht'U (hC.line M hM).1 ht2 (hC.line M hM).2
    refine ⟨X, mem_supp.mpr ⟨hXt, fun h0 => hnotB X hXt ⟨M, hM, hXM⟩
      (hBad X (hXt.trans ht'U) (Or.inr ⟨⟨M, hM, hXM⟩, h0⟩))⟩, hXM⟩
  · intro M hM M' hM'
    by_contra hne
    rw [mem_supp] at hx
    exact hnotB x hx.1 ⟨M, hM.1, hM.2⟩
      (hBad x (hx.1.trans ht'U) (Or.inl ⟨M, hM.1, M', hM'.1, hne, hM.2, hM'.2⟩))

/-- a point of the plane off the configuration -/
theorem cfg_off_pt (hC : Cfg p U c F) (hU : Module.finrank K U = 3) (hq : 33 ≤ Fintype.card K) :
    ∃ H : Lines K N, H.1 ≤ U ∧ ∀ M ∈ F, ¬ H.1 ≤ M := by
  classical
  have hsub : (pts U).filter (fun x => ∃ M ∈ F, x.1 ≤ M) ⊆ F.biUnion pts := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨M, hM, hxM⟩ := hx.2
    exact Finset.mem_biUnion.mpr ⟨M, hM, mem_pts.mpr hxM⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∑ M ∈ F, (pts M).card = ∑ M ∈ F, (Fintype.card K + 1) :=
    Finset.sum_congr rfl (fun M hM => card_line (hC.line M hM).2)
  rw [h2, Finset.sum_const, hC.card, smul_eq_mul] at h1
  have h3 : ((pts U).filter (fun x => ∃ M ∈ F, x.1 ≤ M)).card < (pts U).card := by
    rw [card_plane hU]; nlinarith
  obtain ⟨H, hH, hH'⟩ := Finset.exists_mem_notMem_of_card_lt_card h3
  refine ⟨H, mem_pts.mp hH, fun M hM hHM => hH' (Finset.mem_filter.mpr ⟨hH, M, hM, hHM⟩)⟩

/-- a hole of a 3-secant off the configuration -/
theorem cfg_hole (hC : Cfg p U c F) (hq : 33 ≤ Fintype.card K) {t : Submodule K (Fin N → K)}
    (ht : Module.finrank K t = 2) (h3 : wt t c = 3) :
    ∃ H : Lines K N, H.1 ≤ t ∧ ∀ M ∈ F, ¬ H.1 ≤ M := by
  classical
  have htF := cfg_sec_notin hC hq h3
  have hcov := card_cover ht F (fun M hM => ⟨(hC.line M hM).2, fun h => htF (h ▸ hM)⟩)
    ((pts t).filter (fun x => ∃ M ∈ F, x.1 ≤ M)) (fun x hx => by
      rw [Finset.mem_filter, mem_pts] at hx; exact hx)
  rw [hC.card] at hcov
  have h3 : ((pts t).filter (fun x => ∃ M ∈ F, x.1 ≤ M)).card < (pts t).card := by
    rw [card_line ht]; omega
  obtain ⟨H, hH, hH'⟩ := Finset.exists_mem_notMem_of_card_lt_card h3
  exact ⟨H, mem_pts.mp hH, fun M hM hHM => hH' (Finset.mem_filter.mpr ⟨hH, M, hM, hHM⟩)⟩

end ProxGapTight.Dev.Q366.PartP
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace ProxGapTight.Dev.Q366.PartP
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
variable {p : ℕ} {U : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
/-! ## Two- and three-line combinations -/
theorem hyp_fr {A : Submodule K (Fin N → K)} (hU : Module.finrank K U = 3) (hA : IsHyp A U) :
    Module.finrank K A = 2 := by have := hA.2; omega

theorem val2 {A B : Submodule K (Fin N → K)} {α β : ZMod p}
    (hc : c = α • ind p A + β • ind p B) (x : Lines K N) :
    c x = α * ind p A x + β * ind p B x := by
  rw [hc]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem lineA {A B : Submodule K (Fin N → K)} (hA : Module.finrank K A = 2)
    (hB : Module.finrank K B = 2) {α β : ZMod p} (hc : c = α • ind p A + β • ind p B) :
    wt A c ≤ 1 ∨ Fintype.card K ≤ wt A c := by
  by_cases hAB : A = B
  · subst hAB
    by_cases hs : α + β = 0
    · left
      have := wt_le_cover (c := c) hA ∅ (by simp) (fun x hx hcx => by
        rw [val2 hc, ind_le hx] at hcx; exact absurd (by linear_combination hs) hcx)
      simp at this; omega
    · right
      have := wt_ge_cover (c := c) hA ∅ (by simp) (fun x hx _ => by
        rw [val2 hc, ind_le hx]; simpa [← add_mul] using hs)
      simp at this; omega
  · have hF : ∀ M ∈ ({B} : Finset (Submodule K (Fin N → K))), Module.finrank K M = 2 ∧ M ≠ A := by
      intro M hM; rw [Finset.mem_singleton] at hM; subst hM; exact ⟨hB, Ne.symm hAB⟩
    by_cases hα : α = 0
    · left
      have := wt_le_cover (c := c) hA {B} hF (fun x hx hcx => by
        refine ⟨B, Finset.mem_singleton_self _, ?_⟩
        by_contra hxB
        rw [val2 hc, ind_le hx, ind_nle hxB, hα] at hcx; simp at hcx)
      simpa using this
    · right
      have := wt_ge_cover (c := c) hA {B} hF (fun x hx hno => by
        rw [val2 hc, ind_le hx, ind_nle (hno B (Finset.mem_singleton_self _))]; simpa using hα)
      simp at this; omega

theorem two_lines (hU : Module.finrank K U = 3) (h : TwoComb p U c) {L : Submodule K (Fin N → K)}
    (hLU : L ≤ U) (hL : Module.finrank K L = 2) :
    wt L c ≤ 2 ∨ Fintype.card K ≤ wt L c := by
  classical
  obtain ⟨A, B, hA, hB, α, β, hc⟩ := h
  have hA2 := hyp_fr hU hA
  have hB2 := hyp_fr hU hB
  by_cases hLA : L = A
  · subst hLA
    rcases lineA hA2 hB2 hc with h | h
    · left; omega
    · right; exact h
  by_cases hLB : L = B
  · subst hLB
    have hc' : c = β • ind p L + α • ind p A := by rw [hc, add_comm]
    rcases lineA hB2 hA2 hc' with h | h
    · left; omega
    · right; exact h
  left
  have := wt_le_cover (c := c) hL {A, B} (by
      intro M hM
      simp only [Finset.mem_insert, Finset.mem_singleton] at hM
      rcases hM with rfl | rfl
      · exact ⟨hA2, Ne.symm hLA⟩
      · exact ⟨hB2, Ne.symm hLB⟩) (fun x _ hcx => by
      by_contra hno
      simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left,
        not_or] at hno
      rw [val2 hc, ind_nle hno.1, ind_nle hno.2] at hcx; simp at hcx)
  exact this.trans Finset.card_le_two

/-- a nondegenerate three-line combination -/
structure T3 (p : ℕ) (U : Submodule K (Fin N → K)) (c : Lines K N → ZMod p)
    (A1 A2 A3 : Submodule K (Fin N → K)) (α1 α2 α3 : ZMod p) : Prop where
  h1 : A1 ≤ U
  h2 : A2 ≤ U
  h3 : A3 ≤ U
  f1 : Module.finrank K A1 = 2
  f2 : Module.finrank K A2 = 2
  f3 : Module.finrank K A3 = 2
  n12 : A1 ≠ A2
  n13 : A1 ≠ A3
  n23 : A2 ≠ A3
  a1 : α1 ≠ 0
  a2 : α2 ≠ 0
  a3 : α3 ≠ 0
  hc : c = α1 • ind p A1 + α2 • ind p A2 + α3 • ind p A3

theorem tri_or (hU : Module.finrank K U = 3) (h : Tri3 p U c) :
    TwoComb p U c ∨ ∃ A1 A2 A3 : Submodule K (Fin N → K), ∃ α1 α2 α3 : ZMod p,
      T3 p U c A1 A2 A3 α1 α2 α3 := by
  obtain ⟨A1, A2, A3, h1, h2, h3, α1, α2, α3, hc⟩ := h
  have hv : ∀ x, c x = α1 * ind p A1 x + α2 * ind p A2 x + α3 * ind p A3 x := fun x => by
    rw [hc]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases a1 : α1 = 0
  · left; refine ⟨A2, A3, h2, h3, α2, α3, ?_⟩
    funext x; rw [hv, a1]; simp
  by_cases a2 : α2 = 0
  · left; refine ⟨A1, A3, h1, h3, α1, α3, ?_⟩
    funext x; rw [hv, a2]; simp
  by_cases a3 : α3 = 0
  · left; refine ⟨A1, A2, h1, h2, α1, α2, ?_⟩
    funext x; rw [hv, a3]; simp
  by_cases n12 : A1 = A2
  · left; refine ⟨A1, A3, h1, h3, α1 + α2, α3, ?_⟩
    funext x; rw [hv, n12]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  by_cases n13 : A1 = A3
  · left; refine ⟨A1, A2, h1, h2, α1 + α3, α2, ?_⟩
    funext x; rw [hv, n13]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  by_cases n23 : A2 = A3
  · left; refine ⟨A1, A2, h1, h2, α1, α2 + α3, ?_⟩
    funext x; rw [hv, n23]; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  right
  exact ⟨A1, A2, A3, α1, α2, α3, h1.1, h2.1, h3.1, hyp_fr hU h1, hyp_fr hU h2, hyp_fr hU h3,
    n12, n13, n23, a1, a2, a3, hc⟩

open Classical in
theorem t3_val {A1 A2 A3 : Submodule K (Fin N → K)} {α1 α2 α3 : ZMod p}
    (hT : T3 p U c A1 A2 A3 α1 α2 α3) (x : Lines K N) :
    c x = (if x.1 ≤ A1 then α1 else 0) + (if x.1 ≤ A2 then α2 else 0) +
      (if x.1 ≤ A3 then α3 else 0) := by
  rw [hT.hc]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h1 : x.1 ≤ A1 <;> by_cases h2 : x.1 ≤ A2 <;> by_cases h3 : x.1 ≤ A3 <;>
    simp [h1, h2, h3, ind_le, ind_nle]

/-- a zero on the configuration lies on two of its lines -/
theorem t3_zero {A1 A2 A3 : Submodule K (Fin N → K)} {α1 α2 α3 : ZMod p}
    (hT : T3 p U c A1 A2 A3 α1 α2 α3) {x : Lines K N} (hx : c x = 0)
    (hon : x.1 ≤ A1 ∨ x.1 ≤ A2 ∨ x.1 ≤ A3) :
    (x.1 ≤ A1 ∧ x.1 ≤ A2) ∨ (x.1 ≤ A1 ∧ x.1 ≤ A3) ∨ (x.1 ≤ A2 ∧ x.1 ≤ A3) := by
  rw [t3_val hT] at hx
  have a1 := hT.a1
  have a2 := hT.a2
  have a3 := hT.a3
  by_cases h1 : x.1 ≤ A1 <;> by_cases h2 : x.1 ≤ A2 <;> by_cases h3 : x.1 ≤ A3 <;>
    simp_all

/-! ## Weights of three-line configurations -/
theorem heavy_of {A B C : Submodule K (Fin N → K)} (hA : Module.finrank K A = 2)
    (hB : Module.finrank K B = 2) (hC : Module.finrank K C = 2) (nAB : A ≠ B) (nAC : A ≠ C)
    (h : ∀ x : Lines K N, x.1 ≤ A → ¬ x.1 ≤ B → ¬ x.1 ≤ C → c x ≠ 0) :
    Fintype.card K - 1 ≤ wt A c := by
  classical
  have := wt_ge_cover hA {B, C} (by
      intro M hM
      simp only [Finset.mem_insert, Finset.mem_singleton] at hM
      rcases hM with rfl | rfl
      · exact ⟨hB, Ne.symm nAB⟩
      · exact ⟨hC, Ne.symm nAC⟩)
    (fun x hx hno => h x hx (hno B (by simp)) (hno C (by simp)))
  have := Finset.card_le_two (a := B) (b := C)
  omega

theorem tri_cfg {A1 A2 A3 : Submodule K (Fin N → K)} {α1 α2 α3 : ZMod p}
    (hU : Module.finrank K U = 3) (hT : T3 p U c A1 A2 A3 α1 α2 α3) :
    Cfg p U c {A1, A2, A3} := by
  classical
  obtain ⟨V12, v12a, v12b⟩ := meet hU hT.h1 hT.h2 hT.f1 hT.f2
  obtain ⟨V13, v13a, v13b⟩ := meet hU hT.h1 hT.h3 hT.f1 hT.f3
  obtain ⟨V23, v23a, v23b⟩ := meet hU hT.h2 hT.h3 hT.f2 hT.f3
  have hpair : ∀ x : Lines K N, ((x.1 ≤ A1 ∧ x.1 ≤ A2) ∨ (x.1 ≤ A1 ∧ x.1 ≤ A3) ∨
      (x.1 ≤ A2 ∧ x.1 ≤ A3)) → x ∈ ({V12, V13, V23} : Finset (Lines K N)) := by
    rintro x (⟨h1, h2⟩ | ⟨h1, h3⟩ | ⟨h2, h3⟩)
    · rw [eq_pt hT.f1 hT.f2 hT.n12 h1 h2 v12a v12b]; simp
    · rw [eq_pt hT.f1 hT.f3 hT.n13 h1 h3 v13a v13b]; simp
    · rw [eq_pt hT.f2 hT.f3 hT.n23 h2 h3 v23a v23b]; simp
  have hmem : ∀ M ∈ ({A1, A2, A3} : Finset (Submodule K (Fin N → K))),
      M = A1 ∨ M = A2 ∨ M = A3 := by
    intro M hM; simpa using hM
  refine ⟨?_, ?_, ?_, ?_, ⟨{V12, V13, V23}, Finset.card_le_three.trans (by norm_num), ?_⟩⟩
  · exact Finset.card_eq_three.mpr ⟨A1, A2, A3, hT.n12, hT.n13, hT.n23, rfl⟩
  · intro M hM
    rcases hmem M hM with rfl | rfl | rfl
    exacts [⟨hT.h1, hT.f1⟩, ⟨hT.h2, hT.f2⟩, ⟨hT.h3, hT.f3⟩]
  · intro x hx
    by_contra hno
    simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left,
      not_or] at hno
    rw [t3_val hT] at hx; simp [hno.1, hno.2.1, hno.2.2] at hx
  · intro M hM
    rcases hmem M hM with rfl | rfl | rfl
    · exact heavy_of hT.f1 hT.f2 hT.f3 hT.n12 hT.n13 (fun x h1 h2 h3 => by
        rw [t3_val hT]; simpa [h1, h2, h3] using hT.a1)
    · exact heavy_of hT.f2 hT.f1 hT.f3 (Ne.symm hT.n12) hT.n23 (fun x h2 h1 h3 => by
        rw [t3_val hT]; simpa [h1, h2, h3] using hT.a2)
    · exact heavy_of hT.f3 hT.f1 hT.f2 (Ne.symm hT.n13) (Ne.symm hT.n23) (fun x h3 h1 h2 => by
        rw [t3_val hT]; simpa [h1, h2, h3] using hT.a3)
  · intro x _ hx
    rcases hx with ⟨M, hM, M', hM', hne, hxM, hxM'⟩ | ⟨⟨M, hM, hxM⟩, h0⟩
    · rcases hmem M hM with rfl | rfl | rfl <;> rcases hmem M' hM' with rfl | rfl | rfl <;>
        first | exact absurd rfl hne | exact hpair x (by tauto)
    · apply hpair
      apply t3_zero hT h0
      rcases hmem M hM with rfl | rfl | rfl <;> tauto

open Classical in
theorem inter_card (hU : Module.finrank K U = 3) {L M : Submodule K (Fin N → K)} (hLU : L ≤ U)
    (hMU : M ≤ U) (hL : Module.finrank K L = 2) (hM : Module.finrank K M = 2) (hLM : L ≠ M) :
    (pts L ∩ pts M).card = 1 := by
  classical
  obtain ⟨x, hxL, hxM⟩ := meet hU hLU hMU hL hM
  rw [Finset.card_eq_one]; refine ⟨x, ?_⟩
  ext y; simp only [Finset.mem_inter, mem_pts, Finset.mem_singleton]
  constructor
  · rintro ⟨hyL, hyM⟩; exact eq_pt hL hM hLM hyL hyM hxL hxM
  · rintro rfl; exact ⟨hxL, hxM⟩

open Classical in
theorem union_wt (hU : Module.finrank K U = 3) {M1 M2 M3 : Submodule K (Fin N → K)}
    (h1 : M1 ≤ U) (h2 : M2 ≤ U) (h3 : M3 ≤ U) (f1 : Module.finrank K M1 = 2)
    (f2 : Module.finrank K M2 = 2) (f3 : Module.finrank K M3 = 2) (n12 : M1 ≠ M2) (n13 : M1 ≠ M3)
    (n23 : M2 ≠ M3) (hsupp : ∀ x : Lines K N, c x ≠ 0 → x.1 ≤ M1 ∨ x.1 ≤ M2 ∨ x.1 ≤ M3) :
    wt U c + ((pts M1 ∪ pts M2 ∪ pts M3).filter (fun x => c x = 0)).card =
      3 * Fintype.card K + (pts M1 ∩ pts M2 ∩ pts M3).card := by
  have e12 := inter_card hU h1 h2 f1 f2 n12
  have e13 := inter_card hU h1 h3 f1 f3 n13
  have e23 := inter_card hU h2 h3 f2 f3 n23
  have hA := Finset.card_union_add_card_inter (pts M1) (pts M2)
  have hB := Finset.card_union_add_card_inter (pts M1 ∪ pts M2) (pts M3)
  rw [Finset.union_inter_distrib_right] at hB
  have hC := Finset.card_union_add_card_inter (pts M1 ∩ pts M3) (pts M2 ∩ pts M3)
  have hD : pts M1 ∩ pts M3 ∩ (pts M2 ∩ pts M3) = pts M1 ∩ pts M2 ∩ pts M3 := by
    ext x; simp only [Finset.mem_inter]; tauto
  rw [hD] at hC
  have hs : supp U c = (pts M1 ∪ pts M2 ∪ pts M3).filter (fun x => c x ≠ 0) := by
    ext x; simp only [mem_supp, Finset.mem_filter, Finset.mem_union, mem_pts]
    constructor
    · rintro ⟨_, hcx⟩
      exact ⟨by rcases hsupp x hcx with h | h | h <;> tauto, hcx⟩
    · rintro ⟨hx, hcx⟩
      refine ⟨?_, hcx⟩
      rcases hx with (h | h) | h
      exacts [h.trans h1, h.trans h2, h.trans h3]
  have hF := Finset.card_filter_add_card_filter_not (s := pts M1 ∪ pts M2 ∪ pts M3)
    (fun x => c x ≠ 0)
  have hZ : (pts M1 ∪ pts M2 ∪ pts M3).filter (fun x => ¬ c x ≠ 0) =
      (pts M1 ∪ pts M2 ∪ pts M3).filter (fun x => c x = 0) :=
    Finset.filter_congr (fun x _ => not_not)
  rw [hZ] at hF
  rw [wt_eq, hs]
  rw [card_line f1, card_line f2] at hA
  rw [card_line f3] at hB
  omega

open Classical in
theorem triple_one {M1 M2 M3 : Submodule K (Fin N → K)} {C : Lines K N} (hU : Module.finrank K U = 3)
    (h1 : M1 ≤ U) (h2 : M2 ≤ U) (f1 : Module.finrank K M1 = 2)
    (f2 : Module.finrank K M2 = 2) (n12 : M1 ≠ M2) (c1 : C.1 ≤ M1) (c2 : C.1 ≤ M2) (c3 : C.1 ≤ M3) :
    (pts M1 ∩ pts M2 ∩ pts M3).card = 1 := by
  have e12 := inter_card hU h1 h2 f1 f2 n12
  have hle := Finset.card_le_card (Finset.inter_subset_left (s₁ := pts M1 ∩ pts M2) (s₂ := pts M3))
  have hpos : 0 < (pts M1 ∩ pts M2 ∩ pts M3).card :=
    Finset.card_pos.mpr ⟨C, by simp [Finset.mem_inter, mem_pts, c1, c2, c3]⟩
  omega

open Classical in
theorem triple_zero {M1 M2 M3 : Submodule K (Fin N → K)}
    (hno : ¬ ∃ C : Lines K N, C.1 ≤ M1 ∧ C.1 ≤ M2 ∧ C.1 ≤ M3) :
    (pts M1 ∩ pts M2 ∩ pts M3).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro x hx
  simp only [Finset.mem_inter, mem_pts] at hx
  exact hno ⟨x, hx.1.1, hx.1.2, hx.2⟩

end ProxGapTight.Dev.Q366.PartP
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace ProxGapTight.Dev.Q366.PartP
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
variable {p : ℕ} {U : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
  {A1 A2 A3 : Submodule K (Fin N → K)} {α1 α2 α3 : ZMod p}
theorem t3_supp (hT : T3 p U c A1 A2 A3 α1 α2 α3) :
    ∀ x : Lines K N, c x ≠ 0 → x.1 ≤ A1 ∨ x.1 ≤ A2 ∨ x.1 ≤ A3 := fun x hx => by
  by_contra hno
  simp only [not_or] at hno
  rw [t3_val hT] at hx; simp [hno.1, hno.2.1, hno.2.2] at hx

open Classical in
theorem tri_conc (hU : Module.finrank K U = 3) (hT : T3 p U c A1 A2 A3 α1 α2 α3) {C : Lines K N}
    (c1 : C.1 ≤ A1) (c2 : C.1 ≤ A2) (c3 : C.1 ≤ A3) :
    3 * Fintype.card K ≤ wt U c ∧ (α1 + α2 + α3 = 0 → wt U c = 3 * Fintype.card K) ∧
      (α1 + α2 + α3 ≠ 0 → wt U c = 3 * Fintype.card K + 1) := by
  have hw := union_wt hU hT.h1 hT.h2 hT.h3 hT.f1 hT.f2 hT.f3 hT.n12 hT.n13 hT.n23 (t3_supp hT)
  rw [triple_one hU hT.h1 hT.h2 hT.f1 hT.f2 hT.n12 c1 c2 c3] at hw
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (pts A1 ∪ pts A2 ∪ pts A3).filter (fun x => c x = 0) := ⟨_, rfl⟩
  rw [← hZ] at hw
  have hZC : Z ⊆ {C} := by
    intro z hz
    rw [hZ, Finset.mem_filter] at hz
    simp only [Finset.mem_union, mem_pts] at hz
    have hon : z.1 ≤ A1 ∨ z.1 ≤ A2 ∨ z.1 ≤ A3 := by tauto
    rw [Finset.mem_singleton]
    rcases t3_zero hT hz.2 hon with ⟨h1, h2⟩ | ⟨h1, h3⟩ | ⟨h2, h3⟩
    · exact eq_pt hT.f1 hT.f2 hT.n12 h1 h2 c1 c2
    · exact eq_pt hT.f1 hT.f3 hT.n13 h1 h3 c1 c3
    · exact eq_pt hT.f2 hT.f3 hT.n23 h2 h3 c2 c3
  have hcC : c C = α1 + α2 + α3 := by rw [t3_val hT]; simp [c1, c2, c3]
  have hle := Finset.card_le_card hZC
  rw [Finset.card_singleton] at hle
  refine ⟨by omega, fun hs => ?_, fun hs => ?_⟩
  · have hC : C ∈ Z := by
      rw [hZ, Finset.mem_filter]; simp [mem_pts, c1, hcC, hs]
    have := Finset.card_pos.mpr ⟨C, hC⟩; omega
  · have : Z = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]; intro z hz
      have hzC := hZC hz; rw [Finset.mem_singleton] at hzC; subst hzC
      rw [hZ, Finset.mem_filter] at hz; exact hs (hcC ▸ hz.2)
    rw [this, Finset.card_empty] at hw; omega

/-- the tight-plane property: two holes on each configuration line -/
def Tight (p : ℕ) (c : Lines K N → ZMod p) (F : Finset (Submodule K (Fin N → K))) : Prop :=
  ∀ M ∈ F, ∃ z z' : Lines K N, z ≠ z' ∧ z.1 ≤ M ∧ z'.1 ≤ M ∧ c z = 0 ∧ c z' = 0

open Classical in
theorem tri_tri (hU : Module.finrank K U = 3) (hT : T3 p U c A1 A2 A3 α1 α2 α3)
    (hno : ¬ ∃ C : Lines K N, C.1 ≤ A1 ∧ C.1 ≤ A2 ∧ C.1 ≤ A3) :
    wt U c ≤ 3 * Fintype.card K ∧
    (α1 + α2 = 0 → α1 + α3 = 0 → α2 + α3 = 0 →
      wt U c + 3 = 3 * Fintype.card K ∧ Tight p c {A1, A2, A3}) ∧
    (¬ (α1 + α2 = 0 ∧ α1 + α3 = 0 ∧ α2 + α3 = 0) → 3 * Fintype.card K ≤ wt U c + 2) ∧
    (α1 + α2 ≠ 0 → α1 + α3 ≠ 0 → α2 + α3 ≠ 0 → wt U c = 3 * Fintype.card K) := by
  have hw := union_wt hU hT.h1 hT.h2 hT.h3 hT.f1 hT.f2 hT.f3 hT.n12 hT.n13 hT.n23 (t3_supp hT)
  rw [triple_zero hno] at hw
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (pts A1 ∪ pts A2 ∪ pts A3).filter (fun x => c x = 0) := ⟨_, rfl⟩
  rw [← hZ] at hw
  obtain ⟨V12, v12a, v12b⟩ := meet hU hT.h1 hT.h2 hT.f1 hT.f2
  obtain ⟨V13, v13a, v13b⟩ := meet hU hT.h1 hT.h3 hT.f1 hT.f3
  obtain ⟨V23, v23a, v23b⟩ := meet hU hT.h2 hT.h3 hT.f2 hT.f3
  have n3 : ¬ V12.1 ≤ A3 := fun h => hno ⟨V12, v12a, v12b, h⟩
  have n2 : ¬ V13.1 ≤ A2 := fun h => hno ⟨V13, v13a, h, v13b⟩
  have n1 : ¬ V23.1 ≤ A1 := fun h => hno ⟨V23, h, v23a, v23b⟩
  have cv12 : c V12 = α1 + α2 := by rw [t3_val hT]; simp [v12a, v12b, n3]
  have cv13 : c V13 = α1 + α3 := by rw [t3_val hT]; simp [v13a, v13b, n2]
  have cv23 : c V23 = α2 + α3 := by rw [t3_val hT]; simp [v23a, v23b, n1]
  have d1 : V12 ≠ V13 := fun h => n3 (by rw [h]; exact v13b)
  have d2 : V12 ≠ V23 := fun h => n3 (by rw [h]; exact v23b)
  have d3 : V13 ≠ V23 := fun h => n2 (by rw [h]; exact v23a)
  have hZsub : ∀ z ∈ Z, (z = V12 ∧ α1 + α2 = 0) ∨ (z = V13 ∧ α1 + α3 = 0) ∨
      (z = V23 ∧ α2 + α3 = 0) := by
    intro z hz
    rw [hZ, Finset.mem_filter] at hz
    simp only [Finset.mem_union, mem_pts] at hz
    have hon : z.1 ≤ A1 ∨ z.1 ≤ A2 ∨ z.1 ≤ A3 := by tauto
    rcases t3_zero hT hz.2 hon with ⟨h1, h2⟩ | ⟨h1, h3⟩ | ⟨h2, h3⟩
    · have e := eq_pt hT.f1 hT.f2 hT.n12 h1 h2 v12a v12b
      subst e; exact Or.inl ⟨rfl, cv12 ▸ hz.2⟩
    · have e := eq_pt hT.f1 hT.f3 hT.n13 h1 h3 v13a v13b
      subst e; exact Or.inr (Or.inl ⟨rfl, cv13 ▸ hz.2⟩)
    · have e := eq_pt hT.f2 hT.f3 hT.n23 h2 h3 v23a v23b
      subst e; exact Or.inr (Or.inr ⟨rfl, cv23 ▸ hz.2⟩)
  have hmemZ : ∀ V : Lines K N, V.1 ≤ A1 → c V = 0 → V ∈ Z := by
    intro V hV h0; rw [hZ, Finset.mem_filter]; simp [mem_pts, hV, h0]
  have hmemZ2 : ∀ V : Lines K N, V.1 ≤ A2 → c V = 0 → V ∈ Z := by
    intro V hV h0; rw [hZ, Finset.mem_filter]; simp [mem_pts, hV, h0]
  have hZ3 : Z ⊆ {V12, V13, V23} := by
    intro z hz
    rcases hZsub z hz with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  have hZle := (Finset.card_le_card hZ3).trans Finset.card_le_three
  refine ⟨by omega, fun s12 s13 s23 => ⟨?_, ?_⟩, fun hn => ?_, fun s12 s13 s23 => ?_⟩
  · have hsub : ({V12, V13, V23} : Finset (Lines K N)) ⊆ Z := by
      intro V hV
      simp only [Finset.mem_insert, Finset.mem_singleton] at hV
      rcases hV with rfl | rfl | rfl
      · exact hmemZ _ v12a (cv12 ▸ s12)
      · exact hmemZ _ v13a (cv13 ▸ s13)
      · exact hmemZ2 _ v23a (cv23 ▸ s23)
    have h3 : ({V12, V13, V23} : Finset (Lines K N)).card = 3 :=
      Finset.card_eq_three.mpr ⟨V12, V13, V23, d1, d2, d3, rfl⟩
    have := Finset.card_le_card hsub
    omega
  · intro M hM
    simp only [Finset.mem_insert, Finset.mem_singleton] at hM
    rcases hM with rfl | rfl | rfl
    · exact ⟨V12, V13, d1, v12a, v13a, cv12 ▸ s12, cv13 ▸ s13⟩
    · exact ⟨V12, V23, d2, v12b, v23a, cv12 ▸ s12, cv23 ▸ s23⟩
    · exact ⟨V13, V23, d3, v13b, v23b, cv13 ▸ s13, cv23 ▸ s23⟩
  · have : Z.card ≤ 2 := by
      by_cases s12 : α1 + α2 = 0
      · by_cases s13 : α1 + α3 = 0
        · have s23 : α2 + α3 ≠ 0 := fun h => hn ⟨s12, s13, h⟩
          have : Z ⊆ {V12, V13} := by
            intro z hz
            rcases hZsub z hz with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, h⟩
            · simp
            · simp
            · exact absurd h s23
          exact (Finset.card_le_card this).trans Finset.card_le_two
        · have : Z ⊆ {V12, V23} := by
            intro z hz
            rcases hZsub z hz with ⟨rfl, _⟩ | ⟨rfl, h⟩ | ⟨rfl, _⟩
            · simp
            · exact absurd h s13
            · simp
          exact (Finset.card_le_card this).trans Finset.card_le_two
      · have : Z ⊆ {V13, V23} := by
          intro z hz
          rcases hZsub z hz with ⟨rfl, h⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
          · exact absurd h s12
          · simp
          · simp
        exact (Finset.card_le_card this).trans Finset.card_le_two
    omega
  · have : Z = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]; intro z hz
      rcases hZsub z hz with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
      exacts [s12 h, s13 h, s23 h]
    rw [this, Finset.card_empty] at hw; omega

end ProxGapTight.Dev.Q366.PartP
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace ProxGapTight.Dev.Q366.PartP
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
variable {p : ℕ} {U : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
theorem sum_zmod (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) : ∑ y : ZMod p, y = 0 := by
  have h1 : ∑ y : ZMod p, y = ∑ y : ZMod p, -y :=
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun x => (neg_neg x).symm)
  rw [Finset.sum_neg_distrib] at h1
  have h2 : (2 : ZMod p) * ∑ y : ZMod p, y = 0 := by linear_combination h1
  have h3 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  exact (mul_eq_zero.mp h2).resolve_left h3

/-- the odd-type data -/
structure O3 (p : ℕ) (U : Submodule K (Fin N → K)) (c : Lines K N → ZMod p) (S : Lines K N)
    (H1 H2 H3 : Submodule K (Fin N → K)) : Prop where
  h1 : H1 ≤ U
  h2 : H2 ≤ U
  h3 : H3 ≤ U
  f1 : Module.finrank K H1 = 2
  f2 : Module.finrank K H2 = 2
  f3 : Module.finrank K H3 = 2
  s1 : S.1 ≤ H1
  s2 : S.1 ≤ H2
  s3 : S.1 ≤ H3
  n12 : H1 ≠ H2
  n13 : H1 ≠ H3
  n23 : H2 ≠ H3
  supp : ∀ x : Lines K N, c x ≠ 0 → x.1 ≤ H1 ∨ x.1 ≤ H2 ∨ x.1 ≤ H3
  inj : ∀ H, (H = H1 ∨ H = H2 ∨ H = H3) → ∀ x y : Lines K N, x.1 ≤ H → y.1 ≤ H → x ≠ S →
    y ≠ S → c x = c y → x = y

theorem odd_of (hU : Module.finrank K U = 3) (h : OddT p U c) :
    ∃ S : Lines K N, ∃ H1 H2 H3 : Submodule K (Fin N → K), O3 p U c S H1 H2 H3 := by
  obtain ⟨S, H1, H2, H3, h1, h2, h3, s1, s2, s3, n12, n13, n23, hsupp, hinj⟩ := h
  exact ⟨S, H1, H2, H3, h1.1, h2.1, h3.1, hyp_fr hU h1, hyp_fr hU h2, hyp_fr hU h3, s1, s2, s3,
    n12, n13, n23, hsupp, hinj⟩

open Classical in
theorem odd_line [Fact p.Prime] (hp : Fintype.card K = p) (hp2 : p ≠ 2) {S : Lines K N}
    {H : Submodule K (Fin N → K)} (hH : Module.finrank K H = 2) (hS : S.1 ≤ H)
    (hinj : ∀ x y : Lines K N, x.1 ≤ H → y.1 ≤ H → x ≠ S → y ≠ S → c x = c y → x = y) :
    (∃ z : Lines K N, z.1 ≤ H ∧ z ≠ S ∧ c z = 0) ∧ ∑ x ∈ pts H, c x = c S := by
  have hSm : S ∈ pts H := mem_pts.mpr hS
  have hcardT : ((pts H).erase S).card = p := by
    rw [Finset.card_erase_of_mem hSm, card_line hH, hp]; simp
  have hinjOn : Set.InjOn c ((pts H).erase S) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_erase, mem_pts] at hx hy
    exact hinj x y hx.2 hy.2 hx.1 hy.1 hxy
  have himg : ((pts H).erase S).image c = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinjOn, hcardT, ZMod.card]
  refine ⟨?_, ?_⟩
  · have : (0 : ZMod p) ∈ ((pts H).erase S).image c := by rw [himg]; exact Finset.mem_univ _
    obtain ⟨z, hz, hz0⟩ := Finset.mem_image.mp this
    rw [Finset.mem_erase, mem_pts] at hz
    exact ⟨z, hz.2, hz.1, hz0⟩
  · rw [← Finset.add_sum_erase _ _ hSm]
    have : ∑ x ∈ (pts H).erase S, c x = ∑ y ∈ ((pts H).erase S).image c, y :=
      (Finset.sum_image (f := fun y => y) hinjOn).symm
    rw [this, himg, sum_zmod p hp2, add_zero]

open Classical in
theorem odd_zeros {S : Lines K N} {H : Submodule K (Fin N → K)}
    (hinj : ∀ x y : Lines K N, x.1 ≤ H → y.1 ≤ H → x ≠ S → y ≠ S → c x = c y → x = y) :
    ((pts H).filter (fun x => x ≠ S ∧ c x = 0)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  rw [Finset.mem_filter, mem_pts] at hx hy
  exact hinj x y hx.1 hy.1 hx.2.1 hy.2.1 (hx.2.2.trans hy.2.2.symm)

open Classical in
theorem odd_heavy {S : Lines K N} {H : Submodule K (Fin N → K)} (hH : Module.finrank K H = 2)
    (hinj : ∀ x y : Lines K N, x.1 ≤ H → y.1 ≤ H → x ≠ S → y ≠ S → c x = c y → x = y) :
    Fintype.card K - 1 ≤ wt H c := by
  have hz := odd_zeros hinj
  have hsub : pts H ⊆ supp H c ∪ insert S ((pts H).filter (fun x => x ≠ S ∧ c x = 0)) := by
    intro x hx
    by_cases hxS : x = S
    · exact Finset.mem_union_right _ (hxS ▸ Finset.mem_insert_self _ _)
    by_cases h0 : c x = 0
    · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
        ⟨hx, hxS, h0⟩))
    · exact Finset.mem_union_left _ (mem_supp.mpr ⟨mem_pts.mp hx, h0⟩)
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h2 := Finset.card_insert_le S ((pts H).filter (fun x => x ≠ S ∧ c x = 0))
  rw [card_line hH, ← wt_eq] at h1
  omega

theorem odd_cfg {S : Lines K N} {H1 H2 H3 : Submodule K (Fin N → K)}
    (hO : O3 p U c S H1 H2 H3) : Cfg p U c {H1, H2, H3} := by
  classical
  have hmem : ∀ M ∈ ({H1, H2, H3} : Finset (Submodule K (Fin N → K))),
      M = H1 ∨ M = H2 ∨ M = H3 := by
    intro M hM; simpa using hM
  have hMS : ∀ M ∈ ({H1, H2, H3} : Finset (Submodule K (Fin N → K))),
      M ≤ U ∧ Module.finrank K M = 2 ∧ S.1 ≤ M := by
    intro M hM
    rcases hmem M hM with rfl | rfl | rfl
    exacts [⟨hO.h1, hO.f1, hO.s1⟩, ⟨hO.h2, hO.f2, hO.s2⟩, ⟨hO.h3, hO.f3, hO.s3⟩]
  let Zf : Submodule K (Fin N → K) → Finset (Lines K N) := fun H =>
    (pts H).filter (fun x => x ≠ S ∧ c x = 0)
  refine ⟨Finset.card_eq_three.mpr ⟨H1, H2, H3, hO.n12, hO.n13, hO.n23, rfl⟩,
    fun M hM => ⟨(hMS M hM).1, (hMS M hM).2.1⟩, ?_, ?_,
    ⟨insert S (Zf H1 ∪ Zf H2 ∪ Zf H3), ?_, ?_⟩⟩
  · intro x hx
    rcases hO.supp x hx with h | h | h
    · exact ⟨H1, by simp, h⟩
    · exact ⟨H2, by simp, h⟩
    · exact ⟨H3, by simp, h⟩
  · intro M hM
    exact odd_heavy (hMS M hM).2.1 (hO.inj M (hmem M hM))
  · have := Finset.card_insert_le S (Zf H1 ∪ Zf H2 ∪ Zf H3)
    have := Finset.card_union_le (Zf H1 ∪ Zf H2) (Zf H3)
    have := Finset.card_union_le (Zf H1) (Zf H2)
    have := odd_zeros (hO.inj H1 (Or.inl rfl))
    have := odd_zeros (hO.inj H2 (Or.inr (Or.inl rfl)))
    have := odd_zeros (hO.inj H3 (Or.inr (Or.inr rfl)))
    simp only [Zf] at *
    omega
  · intro x _ hx
    rcases hx with ⟨M, hM, M', hM', hne, hxM, hxM'⟩ | ⟨⟨M, hM, hxM⟩, h0⟩
    · have := eq_pt (hMS M hM).2.1 (hMS M' hM').2.1 hne hxM hxM' (hMS M hM).2.2 (hMS M' hM').2.2
      rw [this]; exact Finset.mem_insert_self _ _
    · by_cases hxS : x = S
      · rw [hxS]; exact Finset.mem_insert_self _ _
      apply Finset.mem_insert_of_mem
      have hxZ : x ∈ Zf M := Finset.mem_filter.mpr ⟨mem_pts.mpr hxM, hxS, h0⟩
      rcases hmem M hM with rfl | rfl | rfl
      · simp only [Finset.mem_union]; tauto
      · simp only [Finset.mem_union]; tauto
      · simp only [Finset.mem_union]; tauto

open Classical in
theorem odd_wt [Fact p.Prime] (hU : Module.finrank K U = 3) (hp : Fintype.card K = p)
    (hp2 : p ≠ 2) {S : Lines K N} {H1 H2 H3 : Submodule K (Fin N → K)}
    (hO : O3 p U c S H1 H2 H3) :
    (c S ≠ 0 → 3 * Fintype.card K ≤ wt U c + 2) ∧
    (c S = 0 → wt U c + 3 = 3 * Fintype.card K ∧ Tight p c {H1, H2, H3}) := by
  have hw := union_wt hU hO.h1 hO.h2 hO.h3 hO.f1 hO.f2 hO.f3 hO.n12 hO.n13 hO.n23 hO.supp
  rw [triple_one hU hO.h1 hO.h2 hO.f1 hO.f2 hO.n12 hO.s1 hO.s2 hO.s3] at hw
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (pts H1 ∪ pts H2 ∪ pts H3).filter (fun x => c x = 0) := ⟨_, rfl⟩
  rw [← hZ] at hw
  obtain ⟨⟨z1, z1H, z1S, z10⟩, -⟩ := odd_line hp hp2 hO.f1 hO.s1 (hO.inj H1 (Or.inl rfl))
  obtain ⟨⟨z2, z2H, z2S, z20⟩, -⟩ := odd_line hp hp2 hO.f2 hO.s2 (hO.inj H2 (Or.inr (Or.inl rfl)))
  obtain ⟨⟨z3, z3H, z3S, z30⟩, -⟩ := odd_line hp hp2 hO.f3 hO.s3
    (hO.inj H3 (Or.inr (Or.inr rfl)))
  have hZsub : Z ⊆ insert S {z1, z2, z3} := by
    intro z hz
    rw [hZ, Finset.mem_filter] at hz
    simp only [Finset.mem_union, mem_pts] at hz
    by_cases hzS : z = S
    · rw [hzS]; exact Finset.mem_insert_self _ _
    apply Finset.mem_insert_of_mem
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hz with ⟨(h | h) | h, h0⟩
    · exact Or.inl (hO.inj H1 (Or.inl rfl) z z1 h z1H hzS z1S (h0.trans z10.symm))
    · exact Or.inr (Or.inl (hO.inj H2 (Or.inr (Or.inl rfl)) z z2 h z2H hzS z2S
        (h0.trans z20.symm)))
    · exact Or.inr (Or.inr (hO.inj H3 (Or.inr (Or.inr rfl)) z z3 h z3H hzS z3S
        (h0.trans z30.symm)))
  have d12 : z1 ≠ z2 := fun h => z1S (eq_pt hO.f1 hO.f2 hO.n12 z1H (h ▸ z2H) hO.s1 hO.s2)
  have d13 : z1 ≠ z3 := fun h => z1S (eq_pt hO.f1 hO.f3 hO.n13 z1H (h ▸ z3H) hO.s1 hO.s3)
  have d23 : z2 ≠ z3 := fun h => z2S (eq_pt hO.f2 hO.f3 hO.n23 z2H (h ▸ z3H) hO.s2 hO.s3)
  have h3 : ({z1, z2, z3} : Finset (Lines K N)).card = 3 :=
    Finset.card_eq_three.mpr ⟨z1, z2, z3, d12, d13, d23, rfl⟩
  refine ⟨fun hS0 => ?_, fun hS0 => ⟨?_, ?_⟩⟩
  · have : Z ⊆ {z1, z2, z3} := by
      intro z hz
      have hz' := hZsub hz
      rw [Finset.mem_insert] at hz'
      rcases hz' with rfl | h
      · rw [hZ, Finset.mem_filter] at hz; exact absurd hz.2 hS0
      · exact h
    have := Finset.card_le_card this
    omega
  · have hsub : insert S ({z1, z2, z3} : Finset (Lines K N)) ⊆ Z := by
      intro V hV
      simp only [Finset.mem_insert, Finset.mem_singleton] at hV
      rw [hZ, Finset.mem_filter]
      simp only [Finset.mem_union, mem_pts]
      rcases hV with rfl | rfl | rfl | rfl
      · exact ⟨Or.inl (Or.inl hO.s1), hS0⟩
      · exact ⟨Or.inl (Or.inl z1H), z10⟩
      · exact ⟨Or.inl (Or.inr z2H), z20⟩
      · exact ⟨Or.inr z3H, z30⟩
    have hS : S ∉ ({z1, z2, z3} : Finset (Lines K N)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm z1S, Ne.symm z2S, Ne.symm z3S⟩
    have h4 := Finset.card_insert_of_notMem hS
    have := Finset.card_le_card hsub
    have := Finset.card_le_card hZsub
    omega
  · intro M hM
    simp only [Finset.mem_insert, Finset.mem_singleton] at hM
    rcases hM with rfl | rfl | rfl
    · exact ⟨S, z1, Ne.symm z1S, hO.s1, z1H, hS0, z10⟩
    · exact ⟨S, z2, Ne.symm z2S, hO.s2, z2H, hS0, z20⟩
    · exact ⟨S, z3, Ne.symm z3S, hO.s3, z3H, hS0, z30⟩

/-! ## Sums along a 3-secant, tight planes, classification -/
theorem two_of [hp : Fact p.Prime] {α β γ : ZMod p} (ha : α ≠ 0) (s12 : α + β = 0)
    (s13 : α + γ = 0) (s23 : β + γ = 0) : p = 2 := by
  have h2 : (2 : ZMod p) * α = 0 := by linear_combination s12 + s13 - s23
  have h3 : (2 : ZMod p) = 0 := (mul_eq_zero.mp h2).resolve_right ha
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3
  rw [ZMod.natCast_eq_zero_iff] at this
  exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this

theorem z2_sum (hp : p = 2) {α β : ZMod p} (ha : α ≠ 0) (hb : β ≠ 0) : α + β = 0 := by
  subst hp; revert α β; decide

theorem z2_sum3 (hp : p = 2) {α β γ : ZMod p} (ha : α ≠ 0) (hb : β ≠ 0) (hc : γ ≠ 0) :
    α + β + γ ≠ 0 := by
  subst hp; revert α β γ; decide

theorem odd_p (p a : ℕ) (hG : Good p a K) (ha : a = 1) : Fintype.card K = p ∧ p ≠ 2 := by
  obtain ⟨hK, h32, -, -⟩ := hG
  subst ha
  rw [pow_one] at hK h32
  exact ⟨hK, by omega⟩

open Classical in
theorem tri_sigma {A1 A2 A3 : Submodule K (Fin N → K)} {α1 α2 α3 : ZMod p}
    (hU : Module.finrank K U = 3) (hq : 33 ≤ Fintype.card K) (hT : T3 p U c A1 A2 A3 α1 α2 α3)
    {t : Submodule K (Fin N → K)} (htU : t ≤ U) (ht : Module.finrank K t = 2) (h3 : wt t c = 3) :
    ∑ ℓ ∈ pts t, c ℓ = α1 + α2 + α3 := by
  have htF := cfg_sec_notin (tri_cfg hU hT) hq h3
  have t1 : t ≠ A1 := fun h => htF (by rw [h]; simp)
  have t2 : t ≠ A2 := fun h => htF (by rw [h]; simp)
  have t3 : t ≠ A3 := fun h => htF (by rw [h]; simp)
  obtain ⟨y1, y1t, y1A⟩ := meet hU htU hT.h1 ht hT.f1
  obtain ⟨y2, y2t, y2A⟩ := meet hU htU hT.h2 ht hT.f2
  obtain ⟨y3, y3t, y3A⟩ := meet hU htU hT.h3 ht hT.f3
  have hsub : supp t c ⊆ {y1, y2, y3} := by
    intro x hx; rw [mem_supp] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases t3_supp hT x hx.2 with h | h | h
    · exact Or.inl (eq_pt ht hT.f1 t1 hx.1 h y1t y1A)
    · exact Or.inr (Or.inl (eq_pt ht hT.f2 t2 hx.1 h y2t y2A))
    · exact Or.inr (Or.inr (eq_pt ht hT.f3 t3 hx.1 h y3t y3A))
  have hcard : (supp t c).card = 3 := h3
  have heq : supp t c = {y1, y2, y3} :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact Finset.card_le_three)
  have h3' : ({y1, y2, y3} : Finset (Lines K N)).card = 3 := by rw [← heq]; exact hcard
  have d12 : y1 ≠ y2 := by
    intro h
    have : ({y1, y2, y3} : Finset (Lines K N)) ⊆ {y2, y3} := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; rw [h] at hx; tauto
    have := (Finset.card_le_card this).trans Finset.card_le_two; omega
  have d13 : y1 ≠ y3 := by
    intro h
    have : ({y1, y2, y3} : Finset (Lines K N)) ⊆ {y2, y3} := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; rw [h] at hx; tauto
    have := (Finset.card_le_card this).trans Finset.card_le_two; omega
  have d23 : y2 ≠ y3 := by
    intro h
    have : ({y1, y2, y3} : Finset (Lines K N)) ⊆ {y1, y3} := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; rw [h] at hx; tauto
    have := (Finset.card_le_card this).trans Finset.card_le_two; omega
  have n12 : ¬ y1.1 ≤ A2 := fun h => d12 (eq_pt ht hT.f2 t2 y1t h y2t y2A)
  have n13 : ¬ y1.1 ≤ A3 := fun h => d13 (eq_pt ht hT.f3 t3 y1t h y3t y3A)
  have n21 : ¬ y2.1 ≤ A1 := fun h => d12 (eq_pt ht hT.f1 t1 y1t y1A y2t h)
  have n23 : ¬ y2.1 ≤ A3 := fun h => d23 (eq_pt ht hT.f3 t3 y2t h y3t y3A)
  have n31 : ¬ y3.1 ≤ A1 := fun h => d13 (eq_pt ht hT.f1 t1 y1t y1A y3t h)
  have n32 : ¬ y3.1 ≤ A2 := fun h => d23 (eq_pt ht hT.f2 t2 y2t y2A y3t h)
  have cy1 : c y1 = α1 := by rw [t3_val hT]; simp [y1A, n12, n13]
  have cy2 : c y2 = α2 := by rw [t3_val hT]; simp [y2A, n21, n23]
  have cy3 : c y3 = α3 := by rw [t3_val hT]; simp [y3A, n31, n32]
  have hs : ∑ ℓ ∈ pts t, c ℓ = ∑ ℓ ∈ supp t c, c ℓ := by
    unfold supp; rw [Finset.sum_filter_ne_zero]
  rw [hs, heq, Finset.sum_insert (by simp [d12, d13]), Finset.sum_insert (by simp [d23]),
    Finset.sum_singleton, cy1, cy2, cy3]
  ring

theorem odd_sigma (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {c : Lines K N → ZMod p}
    (hc : c ∈ Code p U) (hpK : Fintype.card K = p) (hp2 : p ≠ 2) {S : Lines K N}
    {H1 H2 H3 : Submodule K (Fin N → K)} (hO : O3 p U c S H1 H2 H3)
    {t : Submodule K (Fin N → K)} (htU : t ≤ U) (ht : Module.finrank K t = 2) :
    ∑ ℓ ∈ pts t, c ℓ = c S := by
  obtain ⟨σ, hσ⟩ := line_sum p a hG hc
  rw [hσ t htU (by omega), ← hσ H1 hO.h1 (by rw [hO.f1]),
    (odd_line hpK hp2 hO.f1 hO.s1 (hO.inj H1 (Or.inl rfl))).2]

theorem cfg_P4 {F : Finset (Submodule K (Fin N → K))} (hC : Cfg p U c F) (hTi : Tight p c F)
    (hq : 33 ≤ Fintype.card K) {t : Submodule K (Fin N → K)} (htU : t ≤ U)
    (ht : Module.finrank K t = 2) (h3 : wt t c = 3) {Q : Lines K N} (hQ : Q.1 ≤ t)
    (hcQ : c Q ≠ 0) :
    (∀ L : Submodule K (Fin N → K), L ≤ U → Module.finrank K L = 2 → Q.1 ≤ L →
      wt L c ≤ Fintype.card K - 1) ∧
    ∃ r : Submodule K (Fin N → K), r ≤ U ∧ Module.finrank K r = 2 ∧ Q.1 ≤ r ∧ r ≠ t ∧
      wt r c ≤ 2 := by
  classical
  have htF := cfg_sec_notin hC hq h3
  refine ⟨fun L _ hL _ => ?_, ?_⟩
  · by_cases hLF : L ∈ F
    · obtain ⟨z, z', hzz, hz, hz', c0, c0'⟩ := hTi L hLF
      have hsub : supp L c ⊆ ((pts L).erase z).erase z' := by
        intro x hx; rw [mem_supp] at hx
        refine Finset.mem_erase.mpr ⟨fun h => hx.2 (h ▸ c0'), Finset.mem_erase.mpr
          ⟨fun h => hx.2 (h ▸ c0), mem_pts.mpr hx.1⟩⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hzz, mem_pts.mpr hz'⟩),
        Finset.card_erase_of_mem (mem_pts.mpr hz), card_line hL] at this
      rw [wt_eq]; omega
    · have := cfg_off hC hL hLF; omega
  · obtain ⟨M, hMF, hQM⟩ := hC.supp Q hcQ
    have honly : ∀ M' ∈ F, Q.1 ≤ M' → M' = M := by
      intro M' hM' hQM'
      by_contra hne
      have := wt_le_cover ht (F.erase M') (fun N hN => ⟨(hC.line N (Finset.mem_of_mem_erase hN)).2,
          fun h => htF (h ▸ Finset.mem_of_mem_erase hN)⟩) (fun x hxt hx => by
        obtain ⟨N, hN, hxN⟩ := hC.supp x hx
        by_cases hNM' : N = M'
        · subst hNM'
          have e := eq_pt ht (hC.line N hN).2 (fun h => htF (h ▸ hN)) hxt hxN hQ hQM'
          subst e
          exact ⟨M, Finset.mem_erase.mpr ⟨Ne.symm hne, hMF⟩, hQM⟩
        · exact ⟨N, Finset.mem_erase.mpr ⟨hNM', hN⟩, hxN⟩)
      rw [Finset.card_erase_of_mem hM', hC.card] at this; omega
    have hcard2 : (F.erase M).card = 2 := by rw [Finset.card_erase_of_mem hMF, hC.card]
    obtain ⟨M', hM'⟩ : (F.erase M).Nonempty := by
      rw [← Finset.card_pos, hcard2]; norm_num
    rw [Finset.mem_erase] at hM'
    obtain ⟨z, z', hzz, hz, hz', c0, c0'⟩ := hTi M' hM'.2
    obtain ⟨Z, hZM', hZM, cZ⟩ : ∃ Z : Lines K N, Z.1 ≤ M' ∧ ¬ Z.1 ≤ M ∧ c Z = 0 := by
      by_cases hzM : z.1 ≤ M
      · refine ⟨z', hz', fun hz'M => ?_, c0'⟩
        exact hM'.1 (uniq hzz (hC.line M' hM'.2).2 (hC.line M hMF).2 hz hz' hzM hz'M)
      · exact ⟨z, hz, hzM, c0⟩
    have hQZ : Q ≠ Z := fun h => hcQ (h ▸ cZ)
    have hQM' : ¬ Q.1 ≤ M' := fun h => hM'.1 (honly M' hM'.2 h)
    have hr2 := join_fr hQZ
    have hrU : Q.1 ⊔ Z.1 ≤ U := sup_le (hQ.trans htU) (hZM'.trans (hC.line M' hM'.2).1)
    refine ⟨Q.1 ⊔ Z.1, hrU, hr2, le_sup_left, ?_, ?_⟩
    · intro hrt
      have hZt : Z.1 ≤ t := by rw [← hrt]; exact le_sup_right
      obtain ⟨X, hXM', hXt, hcX⟩ := cfg_meet hC hq ht h3 hM'.2
      have e := eq_pt ht (hC.line M' hM'.2).2 (fun h => htF (h ▸ hM'.2)) hXt hXM' hZt hZM'
      exact hcX (e ▸ cZ)
    · have hrM' : Q.1 ⊔ Z.1 ≠ M' := fun h => hQM' (by rw [← h]; exact le_sup_left)
      have := wt_le_cover hr2 (F.erase M') (fun N hN => by
          rw [Finset.mem_erase] at hN
          refine ⟨(hC.line N hN.2).2, fun hNr => ?_⟩
          have hQN : Q.1 ≤ N := by rw [hNr]; exact le_sup_left
          have hZN : Z.1 ≤ N := by rw [hNr]; exact le_sup_right
          have e := honly N hN.2 hQN
          exact hZM (e ▸ hZN)) (fun x hxr hx => by
          obtain ⟨N, hN, hxN⟩ := hC.supp x hx
          refine ⟨N, Finset.mem_erase.mpr ⟨fun hNM' => ?_, hN⟩, hxN⟩
          subst hNM'
          have e := eq_pt hr2 (hC.line N hN).2 hrM' hxr hxN le_sup_right hZM'
          exact hx (e ▸ cZ))
      rw [Finset.card_erase_of_mem hM'.2, hC.card] at this; omega

theorem classify (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {c : Lines K N → ZMod p}
    (hU : Module.finrank K U = 3) (hc : c ∈ Code p U) (hw : wt U c ≤ 4 * Fintype.card K - 22) :
    TwoComb p U c ∨
      (∃ A1 A2 A3 : Submodule K (Fin N → K), ∃ α1 α2 α3 : ZMod p, T3 p U c A1 A2 A3 α1 α2 α3) ∨
      (a = 1 ∧ ∃ S : Lines K N, ∃ H1 H2 H3 : Submodule K (Fin N → K), O3 p U c S H1 H2 H3) := by
  rcases plane_II p a hG hU hc hw with h | ⟨ha, h⟩
  · rcases tri_or hU h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨ha, odd_of hU h⟩)

theorem classify_cfg (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {c : Lines K N → ZMod p}
    (hU : Module.finrank K U = 3) (hc : c ∈ Code p U) (hw : wt U c ≤ 4 * Fintype.card K - 22) :
    TwoComb p U c ∨ ∃ F, Cfg p U c F := by
  rcases classify p a hG hU hc hw with h | ⟨A1, A2, A3, α1, α2, α3, hT⟩ | ⟨-, S, H1, H2, H3, hO⟩
  · exact Or.inl h
  · exact Or.inr ⟨_, tri_cfg hU hT⟩
  · exact Or.inr ⟨_, odd_cfg hO⟩

end ProxGapTight.Dev.Q366.PartP
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace ProxGapTight.Dev.Q366.PartP
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ## The targets -/
theorem P1 (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hU : Module.finrank K U = 3) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (hw : wt U c ≤ 3 * Fintype.card K - 4) : TwoComb p U c :=
  plane_I p a hG hU hc hw

end ProxGapTight.Dev.Q366.PartP
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ## Part P: planar facts (from the published plane statement) -/
alias P1 := ProxGapTight.Dev.Q366.PartP.P1

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace ProxGapTight.Dev.Q366.PartP
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
theorem P2 (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hU : Module.finrank K U = 3) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (hw : wt U c ≤ 4 * Fintype.card K - 22) {L : Submodule K (Fin N → K)} (hLU : L ≤ U)
    (hL : Module.finrank K L = 2) : wt L c ≤ 3 ∨ Fintype.card K - 1 ≤ wt L c := by
  rcases classify_cfg p a hG hU hc hw with h2 | ⟨F, hC⟩
  · rcases two_lines hU h2 hLU hL with h | h
    · left; omega
    · right; omega
  · exact cfg_lines hC hL

end ProxGapTight.Dev.Q366.PartP
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
alias P2 := ProxGapTight.Dev.Q366.PartP.P2

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace ProxGapTight.Dev.Q366.PartP
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-- a plane containing a 3-secant has weight at least `3q - 3` -/
theorem P3a (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hU : Module.finrank K U = 3) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    {t : Submodule K (Fin N → K)} (htU : t ≤ U) (ht : Module.finrank K t = 2) (h3 : wt t c = 3) :
    3 * Fintype.card K - 3 ≤ wt U c := by
  have hq := q_ge p a hG
  by_contra hlt
  have h2 := P1 p a hG hU hc (by omega)
  rcases two_lines hU h2 htU ht with h | h <;> omega

end ProxGapTight.Dev.Q366.PartP
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
alias P3a := ProxGapTight.Dev.Q366.PartP.P3a

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace ProxGapTight.Dev.Q366.PartP
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-- the weight of a light plane through a 3-secant `t`, in terms of the sum of `c` over `t` -/
theorem P3 (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hU : Module.finrank K U = 3) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (hw : wt U c ≤ 4 * Fintype.card K - 22)
    {t : Submodule K (Fin N → K)} (htU : t ≤ U) (ht : Module.finrank K t = 2) (h3 : wt t c = 3) :
    (wt U c = 3 * Fintype.card K - 3 → p = 2 ∨ (a = 1 ∧ ∑ ℓ ∈ pts t, c ℓ = 0)) ∧
    (p = 2 → wt U c ≠ 3 * Fintype.card K - 2 ∧ wt U c ≠ 3 * Fintype.card K - 1 ∧
      wt U c ≠ 3 * Fintype.card K) ∧
    (a = 1 → p ≠ 2 → ∑ ℓ ∈ pts t, c ℓ = 0 →
      wt U c = 3 * Fintype.card K - 3 ∨ wt U c = 3 * Fintype.card K) ∧
    (a = 1 → ∑ ℓ ∈ pts t, c ℓ ≠ 0 → 3 * Fintype.card K - 2 ≤ wt U c) := by
  have hq := q_ge p a hG
  rcases classify p a hG hU hc hw with h2 | ⟨A1, A2, A3, α1, α2, α3, hT⟩ |
    ⟨ha, S, H1, H2, H3, hO⟩
  · exfalso; rcases two_lines hU h2 htU ht with h | h <;> omega
  · rw [tri_sigma hU hq hT htU ht h3]
    by_cases hcon : ∃ C : Lines K N, C.1 ≤ A1 ∧ C.1 ≤ A2 ∧ C.1 ≤ A3
    · obtain ⟨C, c1, c2, c3⟩ := hcon
      obtain ⟨hge, hs0, hs1⟩ := tri_conc hU hT c1 c2 c3
      refine ⟨fun h => by omega, fun hp2 => ?_, fun _ _ hs => Or.inr (hs0 hs),
        fun _ hs => by rw [hs1 hs]; omega⟩
      rw [hs1 (z2_sum3 hp2 hT.a1 hT.a2 hT.a3)]; omega
    · obtain ⟨hle, hall, hsome, hnone⟩ := tri_tri hU hT hcon
      refine ⟨fun hw3 => ?_, fun hp2 => ?_, fun _ _ hs => ?_, fun ha hs => ?_⟩
      · left
        by_contra hp2
        have := hsome (fun ⟨s12, s13, s23⟩ => hp2 (two_of hT.a1 s12 s13 s23))
        omega
      · have := (hall (z2_sum hp2 hT.a1 hT.a2) (z2_sum hp2 hT.a1 hT.a3)
          (z2_sum hp2 hT.a2 hT.a3)).1
        omega
      · right
        apply hnone
        · intro h; apply hT.a3; linear_combination hs - h
        · intro h; apply hT.a2; linear_combination hs - h
        · intro h; apply hT.a1; linear_combination hs - h
      · have hp2 := (odd_p p a hG ha).2
        have := hsome (fun ⟨s12, s13, s23⟩ => hp2 (two_of hT.a1 s12 s13 s23))
        omega
  · obtain ⟨hpK, hp2⟩ := odd_p p a hG ha
    rw [odd_sigma p a hG hc hpK hp2 hO htU ht]
    obtain ⟨hne, heq⟩ := odd_wt hU hpK hp2 hO
    refine ⟨fun hw3 => Or.inr ⟨ha, ?_⟩, fun h => absurd h hp2, fun _ _ hs => Or.inl ?_,
      fun _ hs => ?_⟩
    · by_contra hS; have := hne hS; omega
    · have := (heq hs).1; omega
    · have := hne hs; omega

end ProxGapTight.Dev.Q366.PartP
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
alias P3 := ProxGapTight.Dev.Q366.PartP.P3

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace ProxGapTight.Dev.Q366.PartP
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-- tight planes through a 3-secant -/
theorem P4 (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hU : Module.finrank K U = 3) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (hw : wt U c = 3 * Fintype.card K - 3)
    {t : Submodule K (Fin N → K)} (htU : t ≤ U) (ht : Module.finrank K t = 2) (h3 : wt t c = 3)
    {Q : Lines K N} (hQ : Q.1 ≤ t) (hcQ : c Q ≠ 0) :
    (∀ L : Submodule K (Fin N → K), L ≤ U → Module.finrank K L = 2 → Q.1 ≤ L →
      wt L c ≤ Fintype.card K - 1) ∧
    ∃ r : Submodule K (Fin N → K), r ≤ U ∧ Module.finrank K r = 2 ∧ Q.1 ≤ r ∧ r ≠ t ∧
      wt r c ≤ 2 := by
  have hq := q_ge p a hG
  have hTF : ∃ F, Cfg p U c F ∧ Tight p c F := by
    rcases classify p a hG hU hc (by omega) with h2 | ⟨A1, A2, A3, α1, α2, α3, hT⟩ |
      ⟨ha, S, H1, H2, H3, hO⟩
    · exfalso; rcases two_lines hU h2 htU ht with h | h <;> omega
    · by_cases hcon : ∃ C : Lines K N, C.1 ≤ A1 ∧ C.1 ≤ A2 ∧ C.1 ≤ A3
      · obtain ⟨C, c1, c2, c3⟩ := hcon
        have := (tri_conc hU hT c1 c2 c3).1; omega
      · obtain ⟨-, hall, hsome, -⟩ := tri_tri hU hT hcon
        by_cases hz : α1 + α2 = 0 ∧ α1 + α3 = 0 ∧ α2 + α3 = 0
        · exact ⟨_, tri_cfg hU hT, (hall hz.1 hz.2.1 hz.2.2).2⟩
        · have := hsome hz; omega
    · obtain ⟨hpK, hp2⟩ := odd_p p a hG ha
      obtain ⟨hne, heq⟩ := odd_wt hU hpK hp2 hO
      by_cases hS : c S = 0
      · exact ⟨_, odd_cfg hO, (heq hS).2⟩
      · have := hne hS; omega
  obtain ⟨F, hC, hTi⟩ := hTF
  exact cfg_P4 hC hTi hq htU ht h3 hQ hcQ

end ProxGapTight.Dev.Q366.PartP
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
alias P4 := ProxGapTight.Dev.Q366.PartP.P4

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace ProxGapTight.Dev.Q366.PartP
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
theorem P5 (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hU : Module.finrank K U = 3) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (hw : wt U c ≤ 4 * Fintype.card K - 22)
    {t : Submodule K (Fin N → K)} (htU : t ≤ U) (ht : Module.finrank K t = 2) (h3 : wt t c = 3) :
    (∃ H : Lines K N, H.1 ≤ t ∧ c H = 0 ∧ ∃ t' : Submodule K (Fin N → K), t' ≤ U ∧
      Module.finrank K t' = 2 ∧ H.1 ≤ t' ∧ t' ≠ t ∧ wt t' c = 3) ∧
    (∀ M t'' : Submodule K (Fin N → K), M ≤ U → Module.finrank K M = 2 → 4 ≤ wt M c →
      t'' ≤ U → Module.finrank K t'' = 2 → wt t'' c = 3 →
      ∃ X : Lines K N, X.1 ≤ M ∧ X.1 ≤ t'' ∧ c X ≠ 0) := by
  have hq := q_ge p a hG
  rcases classify_cfg p a hG hU hc hw with h2 | ⟨F, hC⟩
  · exfalso; rcases two_lines hU h2 htU ht with h | h <;> omega
  refine ⟨?_, ?_⟩
  · obtain ⟨H, hHt, hHF⟩ := cfg_hole hC hq ht h3
    have hcH : c H = 0 := by
      by_contra h
      obtain ⟨M, hM, hHM⟩ := hC.supp H h
      exact hHF M hM hHM
    obtain ⟨t', ht'U, ht'2, hHt', hne, h3'⟩ := cfg_three hC hU hq (hHt.trans htU) hHF t
    exact ⟨H, hHt, hcH, t', ht'U, ht'2, hHt', hne, h3'⟩
  · intro M t'' _ hM h4 _ ht'' h3''
    have hMF : M ∈ F := by
      by_contra h; have := cfg_off hC hM h; omega
    exact cfg_meet hC hq ht'' h3'' hMF

end ProxGapTight.Dev.Q366.PartP
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
alias P5 := ProxGapTight.Dev.Q366.PartP.P5

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace ProxGapTight.Dev.Q366.PartP
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
theorem P6 (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hU : Module.finrank K U = 3) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (hw : wt U c ≤ 4 * Fintype.card K - 22) {L : Submodule K (Fin N → K)} (hLU : L ≤ U)
    (hL : Module.finrank K L = 2) (hq1 : wt L c = Fintype.card K - 1) :
    ∃ t : Submodule K (Fin N → K), t ≤ U ∧ Module.finrank K t = 2 ∧ wt t c = 3 := by
  have hq := q_ge p a hG
  rcases classify_cfg p a hG hU hc hw with h2 | ⟨F, hC⟩
  · exfalso; rcases two_lines hU h2 hLU hL with h | h <;> omega
  obtain ⟨H, hHU, hHF⟩ := cfg_off_pt hC hU hq
  obtain ⟨t', h1, h2, -, -, h3⟩ := cfg_three hC hU hq hHU hHF ⊥
  exact ⟨t', h1, h2, h3⟩

end ProxGapTight.Dev.Q366.PartP
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
alias P6 := ProxGapTight.Dev.Q366.PartP.P6

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace ProxGapTight.Dev.Q366.PartA
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ### Numerics -/
lemma th_zero (q : ℕ) : th q 0 = 0 := by simp [th]

lemma th_succ (q k : ℕ) : th q (k + 1) = q * th q k + 1 := by
  unfold th
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ, pow_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma th_one (q : ℕ) : th q 1 = 1 := by simp [th]

lemma th_two (q : ℕ) : th q 2 = q + 1 := by rw [th_succ, th_one]; ring

lemma pow_th (q k : ℕ) : ((q : ℤ) ^ k) = ((q : ℤ) - 1) * (th q k : ℤ) + 1 := by
  induction k with
  | zero => simp [th_zero]
  | succ k ih => rw [th_succ, pow_succ, ih]; push_cast; ring

lemma Wb_int (q n : ℕ) (hq : 2 ≤ q) (hn : 3 ≤ n) :
    (Wb q n : ℤ) = 3 * ((q : ℤ) - 1) * (((q : ℤ) - 1) * (th q (n - 3) : ℤ) + 1) - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : m + 3 - 2 = m + 1 := by omega
  have e2 : m + 3 - 3 = m := by omega
  have hu : 1 ≤ q ^ m := Nat.one_le_pow _ _ (by omega)
  have hle : 3 * q ^ m + 1 ≤ 3 * (q ^ m * q) := by nlinarith
  have hW : Wb q (m + 3) + 1 + 3 * q ^ m = 3 * (q ^ m * q) := by
    unfold Wb; rw [e1, e2, pow_succ]; omega
  have h := congrArg (fun x : ℕ => (x : ℤ)) hW
  push_cast at h
  rw [e2]
  have hp := pow_th q m
  linear_combination h + 3 * ((q : ℤ) - 1) * hp

lemma q_ge (p a : ℕ) [hp : Fact p.Prime] (hG : Good p a K) : 37 ≤ Fintype.card K := by
  obtain ⟨hq, h32, h49, h121⟩ := hG
  rw [hq]
  have key : ∀ r : ℕ, r.Prime → r ∣ p ^ a → r = p := fun r hr hd =>
    (Nat.prime_dvd_prime_iff_eq hr hp.out).mp (hr.dvd_of_dvd_pow hd)
  by_contra hlt
  have h4 : p ^ a = 33 ∨ p ^ a = 34 ∨ p ^ a = 35 ∨ p ^ a = 36 := by omega
  rcases h4 with h | h | h | h
  · have e1 := key 3 (by norm_num) (by rw [h]; norm_num)
    have e2 := key 11 (by norm_num) (by rw [h]; norm_num)
    omega
  · have e1 := key 2 (by norm_num) (by rw [h]; norm_num)
    have e2 := key 17 (by norm_num) (by rw [h]; norm_num)
    omega
  · have e1 := key 5 (by norm_num) (by rw [h]; norm_num)
    have e2 := key 7 (by norm_num) (by rw [h]; norm_num)
    omega
  · have e1 := key 2 (by norm_num) (by rw [h]; norm_num)
    have e2 := key 3 (by norm_num) (by rw [h]; norm_num)
    omega

/-! ### Basic API -/
lemma mem_pts {U : Submodule K (Fin N → K)} {ℓ : Lines K N} : ℓ ∈ pts U ↔ ℓ.1 ≤ U := by
  simp [pts]

lemma mem_ext {T U V : Submodule K (Fin N → K)} :
    V ∈ ProxGapTight.Dev.Q366.ext T U ↔
      T ≤ V ∧ V ≤ U ∧ Module.finrank K V = Module.finrank K T + 1 := by
  simp [ProxGapTight.Dev.Q366.ext]

/-- the support of `c` in `U` -/
noncomputable def supp {p : ℕ} (U : Submodule K (Fin N → K)) (c : Lines K N → ZMod p) :
    Finset (Lines K N) := by
  classical exact (pts U).filter (fun ℓ => c ℓ ≠ 0)

lemma wt_eq {p : ℕ} (U : Submodule K (Fin N → K)) (c : Lines K N → ZMod p) :
    wt U c = (supp U c).card := rfl

lemma mem_supp {p : ℕ} {U : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
    {ℓ : Lines K N} : ℓ ∈ supp U c ↔ ℓ.1 ≤ U ∧ c ℓ ≠ 0 := by
  unfold supp; simp [mem_pts]

lemma eq_of_fr {T U : Submodule K (Fin N → K)} (h : T ≤ U)
    (h' : Module.finrank K U ≤ Module.finrank K T) : T = U :=
  Submodule.eq_of_le_of_finrank_le h h'

lemma line_eq_of_le {Y X : Lines K N} (h : Y.1 ≤ X.1) : Y = X :=
  Subtype.ext (eq_of_fr h (by rw [Y.2, X.2]))

lemma join_fr {x y : Lines K N} (hxy : x ≠ y) : Module.finrank K ↥(x.1 ⊔ y.1) = 2 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq x.1 y.1
  have h0 : Module.finrank K ↥(x.1 ⊓ y.1) = 0 := by
    have h2 : Module.finrank K ↥(x.1 ⊓ y.1) ≤ 1 := by
      have := Submodule.finrank_mono (inf_le_left : x.1 ⊓ y.1 ≤ x.1); rw [x.2] at this
      exact this
    by_contra h0
    have e := eq_of_fr (inf_le_left : x.1 ⊓ y.1 ≤ x.1) (by rw [x.2]; omega)
    apply hxy
    apply line_eq_of_le
    rw [← e]; exact inf_le_right
  rw [h0, x.2, y.2] at h1; omega

lemma join_eq {x y : Lines K N} (hxy : x ≠ y) {L : Submodule K (Fin N → K)}
    (hL : Module.finrank K L = 2) (hx : x.1 ≤ L) (hy : y.1 ≤ L) : x.1 ⊔ y.1 = L :=
  eq_of_fr (sup_le hx hy) (by rw [hL, join_fr hxy])

lemma uniq {x y : Lines K N} (hxy : x ≠ y) {L M : Submodule K (Fin N → K)}
    (hL : Module.finrank K L = 2) (hM : Module.finrank K M = 2) (hxL : x.1 ≤ L) (hyL : y.1 ≤ L)
    (hxM : x.1 ≤ M) (hyM : y.1 ≤ M) : L = M := by
  rw [← join_eq hxy hL hxL hyL, join_eq hxy hM hxM hyM]

/-- two distinct lines share at most one point -/
lemma eq_pt {x y : Lines K N} {L M : Submodule K (Fin N → K)}
    (hL : Module.finrank K L = 2) (hM : Module.finrank K M = 2) (hLM : L ≠ M) (hxL : x.1 ≤ L)
    (hxM : x.1 ≤ M) (hyL : y.1 ≤ L) (hyM : y.1 ≤ M) : x = y := by
  by_contra h; exact hLM (uniq h hL hM hxL hyL hxM hyM)

lemma wt_point {p : ℕ} {c : Lines K N → ZMod p} {P : Lines K N} (hP : c P ≠ 0) :
    wt P.1 c = 1 := by
  rw [wt_eq, Finset.card_eq_one]
  refine ⟨P, ?_⟩
  ext ℓ
  rw [mem_supp, Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩; exact line_eq_of_le h
  · rintro rfl; exact ⟨le_rfl, hP⟩

/-! ### Planes inside `U` -/
/-- P2 transported to a plane of `U` -/
lemma light_line (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    {c : Lines K N → ZMod p} (hc : c ∈ Code p U) {τ : Submodule K (Fin N → K)} (hτU : τ ≤ U)
    (hτ : Module.finrank K τ = 3) (hw : wt τ c ≤ 4 * Fintype.card K - 22)
    {L : Submodule K (Fin N → K)} (hLτ : L ≤ τ) (hL : Module.finrank K L = 2) :
    wt L c ≤ 3 ∨ Fintype.card K - 1 ≤ wt L c := by
  have hr := res_mem p a hG hc hτU (by omega)
  have h := P2 p a hG hτ hr (by rw [wt_res τ τ le_rfl c]; exact hw) hLτ hL
  rwa [wt_res L τ hLτ c] at h

/-- the lines of a plane `τ` through a support point `P` partition the support of `τ`; so if
`τ` is heavy compared with a line `L ∋ P`, a second line through `P` carries `≥ 4` points -/
lemma other_line {p : ℕ} {c : Lines K N → ZMod p} {τ L : Submodule K (Fin N → K)}
    (hτ : Module.finrank K τ = 3) (hLτ : L ≤ τ) (hL : Module.finrank K L = 2) {P : Lines K N}
    (hPL : P.1 ≤ L) (hcP : c P ≠ 0) (hbig : wt L c + 2 * Fintype.card K < wt τ c) :
    ∃ M : Submodule K (Fin N → K), M ≤ τ ∧ Module.finrank K M = 2 ∧ M ≠ L ∧ P.1 ≤ M ∧
      4 ≤ wt M c := by
  classical
  have hPτ : P.1 ≤ τ := hPL.trans hLτ
  have h := ext_partition hPτ c
  rw [ext_card hPτ, hτ, P.2, wt_point hcP, show 3 - 1 = 2 from rfl, th_two] at h
  have hLmem : L ∈ ProxGapTight.Dev.Q366.ext P.1 τ := mem_ext.mpr ⟨hPL, hLτ, by rw [hL, P.2]⟩
  rw [← Finset.sum_erase_add _ _ hLmem] at h
  have hcard : ((ProxGapTight.Dev.Q366.ext P.1 τ).erase L).card = Fintype.card K := by
    rw [Finset.card_erase_of_mem hLmem, ext_card hPτ, hτ, P.2, show 3 - 1 = 2 from rfl, th_two]
    omega
  by_contra hno
  push Not at hno
  have hle : ∑ M ∈ (ProxGapTight.Dev.Q366.ext P.1 τ).erase L, wt M c ≤
      ((ProxGapTight.Dev.Q366.ext P.1 τ).erase L).card * 3 := by
    apply Finset.sum_le_card_nsmul
    intro M hM
    obtain ⟨hML, hM'⟩ := Finset.mem_erase.mp hM
    obtain ⟨hPM, hMτ, hMd⟩ := mem_ext.mp hM'
    have := hno M hMτ (by rw [hMd, P.2]) hML hPM
    omega
  rw [hcard] at hle
  nlinarith

/-- a union of sets of size `≥ r`, pairwise meeting in at most one element -/
lemma union_bound {α ι : Type} [DecidableEq α] [DecidableEq ι] (A : ι → Finset α) (r : ℕ)
    (I : Finset ι) (hA : ∀ i ∈ I, r ≤ (A i).card)
    (hI : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (A i ∩ A j).card ≤ 1) :
    2 * I.card * r ≤ 2 * (I.biUnion A).card + I.card * (I.card - 1) := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I haI ih =>
    have ih' := ih (fun i hi => hA i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj hij => hI i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
    rw [Finset.biUnion_insert, Finset.card_insert_of_notMem haI]
    have hu := Finset.card_union_add_card_inter (A a) (I.biUnion A)
    have hint : (A a ∩ I.biUnion A).card ≤ I.card := by
      rw [Finset.inter_biUnion]
      refine Finset.card_biUnion_le.trans ?_
      have : ∑ i ∈ I, (A a ∩ A i).card ≤ I.card * 1 := by
        apply Finset.sum_le_card_nsmul
        intro i hi
        exact hI a (Finset.mem_insert_self a I) i (Finset.mem_insert_of_mem hi)
          (fun h => haI (h ▸ hi))
      simpa using this
    have hAa := hA a (Finset.mem_insert_self a I)
    have e : (I.card + 1) * (I.card + 1 - 1) = I.card * (I.card - 1) + 2 * I.card := by
      rcases Nat.eq_zero_or_pos I.card with h | h
      · rw [h]
      · obtain ⟨k, hk⟩ : ∃ k, I.card = k + 1 := ⟨I.card - 1, by omega⟩
        rw [hk]; simp only [Nat.add_sub_cancel]; ring
    rw [e]
    have e2 : 2 * (I.card + 1) * r = 2 * I.card * r + 2 * r := by ring
    rw [e2]
    omega

/-- telescoping inside a plane: lines `M_P` through `k` points `P` of a line `L`, each with
`≥ s` support points -/
lemma tele {p : ℕ} {c : Lines K N → ZMod p} {τ L : Submodule K (Fin N → K)}
    (hLτ : L ≤ τ) (hL : Module.finrank K L = 2) (X : Finset (Lines K N))
    (hX : ∀ P ∈ X, P.1 ≤ L) (s : ℕ)
    (hM : ∀ P ∈ X, ∃ M : Submodule K (Fin N → K), M ≤ τ ∧ Module.finrank K M = 2 ∧ M ≠ L ∧
      P.1 ≤ M ∧ s ≤ wt M c) :
    2 * wt L c + 2 * X.card * (s - 1) ≤ 2 * wt τ c + X.card * (X.card - 1) := by
  classical
  choose! M hMτ hMd hML hPM hMs using hM
  let A : Lines K N → Finset (Lines K N) := fun P => (supp (M P) c).filter (fun ℓ => ¬ ℓ.1 ≤ L)
  have hA : ∀ P ∈ X, s - 1 ≤ (A P).card := by
    intro P hP
    have hsub : supp (M P) c ⊆ insert P (A P) := by
      intro ℓ hℓ
      by_cases hℓL : ℓ.1 ≤ L
      · rw [Finset.mem_insert]; left
        exact eq_pt (hMd P hP) hL (hML P hP) (mem_supp.mp hℓ).1 hℓL (hPM P hP) (hX P hP)
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hℓ, hℓL⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le P (A P)
    have h3 := hMs P hP
    rw [wt_eq] at h3
    omega
  have hI : ∀ P ∈ X, ∀ P' ∈ X, P ≠ P' → (A P ∩ A P').card ≤ 1 := by
    intro P hP P' hP' hne
    have hMne : M P ≠ M P' := by
      intro heq
      apply hML P hP
      exact uniq hne (hMd P hP) hL (hPM P hP) (heq ▸ hPM P' hP') (hX P hP) (hX P' hP')
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [A, Finset.mem_inter, Finset.mem_filter, mem_supp] at hx hy
    exact eq_pt (hMd P hP) (hMd P' hP') hMne hx.1.1.1 hx.2.1.1 hy.1.1.1 hy.2.1.1
  have hU := union_bound A (s - 1) X hA hI
  have hdisj : Disjoint (supp L c) (X.biUnion A) := by
    rw [Finset.disjoint_left]
    intro ℓ hℓ hℓ'
    obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.mp hℓ'
    exact (Finset.mem_filter.mp hP).2 (mem_supp.mp hℓ).1
  have hsub : supp L c ∪ X.biUnion A ⊆ supp τ c := by
    intro ℓ hℓ
    rcases Finset.mem_union.mp hℓ with h | h
    · exact mem_supp.mpr ⟨(mem_supp.mp h).1.trans hLτ, (mem_supp.mp h).2⟩
    · obtain ⟨P, hP, hℓP⟩ := Finset.mem_biUnion.mp h
      have h' := (mem_supp.mp (Finset.mem_filter.mp hℓP).1)
      exact mem_supp.mpr ⟨h'.1.trans (hMτ P hP), h'.2⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hc
  rw [wt_eq, wt_eq]
  have e : 2 * X.card * (s - 1) = 2 * X.card * (s - 1) := rfl
  omega

/-- choose `k` support points on a line and telescope with `s = k` -/
lemma tele' {p : ℕ} {c : Lines K N → ZMod p} {τ L : Submodule K (Fin N → K)}
    (hLτ : L ≤ τ) (hL : Module.finrank K L = 2) (k : ℕ) (hk : k ≤ wt L c)
    (hM : ∀ P : Lines K N, P.1 ≤ L → c P ≠ 0 → ∃ M : Submodule K (Fin N → K), M ≤ τ ∧
      Module.finrank K M = 2 ∧ M ≠ L ∧ P.1 ≤ M ∧ k ≤ wt M c) :
    2 * wt L c + k * (k - 1) ≤ 2 * wt τ c := by
  rw [wt_eq] at hk
  obtain ⟨X, hXs, hXk⟩ := Finset.exists_subset_card_eq hk
  have h := tele hLτ hL X (fun P hP => (mem_supp.mp (hXs hP)).1) k
    (fun P hP => hM P (mem_supp.mp (hXs hP)).1 (mem_supp.mp (hXs hP)).2)
  rw [hXk] at h
  have e : 2 * k * (k - 1) = k * (k - 1) + k * (k - 1) := by ring
  omega

/-- the count over planes through a line `L`: if every plane through `L` exceeds `L` by at least
`3q - 3`, then the weight exceeds `Wb` -/
lemma planes_bound {p : ℕ} {U : Submodule K (Fin N → K)} (hD : 4 ≤ Module.finrank K U)
    {c : Lines K N → ZMod p} (hq : 2 ≤ Fintype.card K)
    (hw : wt U c ≤ Wb (Fintype.card K) (Module.finrank K U))
    {L : Submodule K (Fin N → K)} (hLU : L ≤ U) (hL : Module.finrank K L = 2) (B : ℕ)
    (hB : 3 * Fintype.card K - 3 ≤ B)
    (h : ∀ τ ∈ ProxGapTight.Dev.Q366.ext L U, wt L c + B ≤ wt τ c) : False := by
  have hp := ext_partition hLU c
  rw [ext_card hLU, hL] at hp
  have hs := Finset.card_nsmul_le_sum _ (fun τ => wt τ c) _ h
  rw [ext_card hLU, hL, smul_eq_mul] at hs
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank K U = n + 4 := ⟨Module.finrank K U - 4, by omega⟩
  rw [hn] at hp hs hw
  rw [show n + 4 - 2 = (n + 1) + 1 by omega, th_succ] at hp hs
  have hW := Wb_int (Fintype.card K) (n + 4) hq (by omega)
  rw [show n + 4 - 3 = n + 1 by omega] at hW
  set q := Fintype.card K
  set x := th q (n + 1)
  set m := wt L c
  have hx : 1 ≤ x := by simp only [x]; rw [th_succ]; omega
  have hB' : (3 * (q : ℤ) - 3) ≤ B := by
    have : 3 * q ≤ B + 3 := by omega
    zify at this; linarith
  zify at hp hs hw
  have : (0 : ℤ) ≤ ((q : ℤ) - 1) * x := by
    apply mul_nonneg <;> [linarith [(by exact_mod_cast hq : (2 : ℤ) ≤ q)]; positivity]
  nlinarith [mul_le_mul_of_nonneg_left hB' (by positivity : (0 : ℤ) ≤ (q : ℤ) * x + 1)]

/-! ### A: lines are short or long -/
/-- every plane through a line `L` of `U` with `4 ≤ wt ≤ q - 2` is heavy -/
lemma planes_heavy (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    {c : Lines K N → ZMod p} (hc : c ∈ Code p U) {L : Submodule K (Fin N → K)}
    (hL : Module.finrank K L = 2) (h4 : 4 ≤ wt L c) (hq2 : wt L c ≤ Fintype.card K - 2)
    {τ : Submodule K (Fin N → K)} (hLτ : L ≤ τ) (hτU : τ ≤ U) (hτ : Module.finrank K τ = 3) :
    4 * Fintype.card K - 21 ≤ wt τ c := by
  by_contra hlt
  rcases light_line p a hG hc hτU hτ (by omega) hLτ hL with h | h <;> omega

/-- A1: no `m`-secant with `4 ≤ m ≤ q - 18` -/
lemma A1 (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hD : 4 ≤ Module.finrank K U) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (hw : wt U c ≤ Wb (Fintype.card K) (Module.finrank K U))
    {L : Submodule K (Fin N → K)} (hLU : L ≤ U) (hL : Module.finrank K L = 2)
    (h4 : 4 ≤ wt L c) (h18 : wt L c + 18 ≤ Fintype.card K) : False := by
  have hq := q_ge p a hG
  refine planes_bound hD (by omega) hw hLU hL (3 * Fintype.card K - 3) le_rfl (fun τ hτ => ?_)
  obtain ⟨hLτ, hτU, hτd⟩ := mem_ext.mp hτ
  have := planes_heavy p a hG hc hL h4 (by omega) hLτ hτU (by rw [hτd, hL])
  omega

theorem A_lines (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hD : 4 ≤ Module.finrank K U) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (hw : wt U c ≤ Wb (Fintype.card K) (Module.finrank K U))
    {L : Submodule K (Fin N → K)} (hLU : L ≤ U) (hL : Module.finrank K L = 2) :
    wt L c ≤ 3 ∨ Fintype.card K - 1 ≤ wt L c := by
  have hq := q_ge p a hG
  by_contra hcon
  push Not at hcon
  obtain ⟨h4, hq2⟩ := hcon
  by_cases h18 : wt L c + 18 ≤ Fintype.card K
  · exact A1 p a hG hD hc hw hLU hL (by omega) h18
  -- A2
  refine planes_bound hD (by omega) hw hLU hL ((Fintype.card K - 17) * (Fintype.card K - 18) / 2) ?_ (fun τ hτ => ?_)
  · obtain ⟨r, hr⟩ : ∃ r, Fintype.card K = r + 37 := ⟨Fintype.card K - 37, by omega⟩
    rw [hr, show r + 37 - 17 = r + 20 by omega, show r + 37 - 18 = r + 19 by omega]
    apply Nat.le_div_iff_mul_le (by norm_num) |>.mpr
    rw [show 3 * (r + 37) - 3 = 3 * r + 108 by omega]
    nlinarith
  obtain ⟨hLτ, hτU, hτd⟩ := mem_ext.mp hτ
  have hτ3 : Module.finrank K τ = 3 := by rw [hτd, hL]
  have hheavy := planes_heavy p a hG hc hL (by omega) (by omega) hLτ hτU hτ3
  have ht := tele' (c := c) hLτ hL (Fintype.card K - 17) (by omega) (fun P hPL hcP => by
    obtain ⟨M, hMτ, hMd, hML, hPM, hM4⟩ := other_line hτ3 hLτ hL hPL hcP (by omega)
    refine ⟨M, hMτ, hMd, hML, hPM, ?_⟩
    by_contra hlt
    exact A1 p a hG hD hc hw (hMτ.trans hτU) hMd hM4 (by omega))
  have e := Nat.div_mul_le_self ((Fintype.card K - 17) * (Fintype.card K - 18)) 2
  rw [show Fintype.card K - 17 - 1 = Fintype.card K - 18 by omega] at ht
  omega

end ProxGapTight.Dev.Q366.PartA
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ## Part A: lines are short or long; heavy planes are very heavy -/
alias A_lines := ProxGapTight.Dev.Q366.PartA.A_lines

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace ProxGapTight.Dev.Q366.PartA
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ### O: heavy planes are very heavy -/
theorem O_heavy (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hD : 4 ≤ Module.finrank K U) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (hw : wt U c ≤ Wb (Fintype.card K) (Module.finrank K U))
    {π : Submodule K (Fin N → K)} (hπU : π ≤ U) (hπ : Module.finrank K π = 3)
    (hheavy : 4 * Fintype.card K - 21 ≤ wt π c) :
    Fintype.card K * (Fintype.card K - 1) / 2 ≤ wt π c := by
  classical
  have hq := q_ge p a hG
  -- a support point
  obtain ⟨X, hX⟩ : ∃ X, X ∈ supp π c := by
    rw [← Finset.nonempty_def, ← Finset.card_pos, ← wt_eq]; omega
  obtain ⟨hXπ, hcX⟩ := mem_supp.mp hX
  -- some line through `X`
  have hne : (ProxGapTight.Dev.Q366.ext X.1 π).Nonempty := by
    rw [← Finset.card_pos, ext_card hXπ, hπ, X.2, show 3 - 1 = 2 from rfl, th_two]; omega
  obtain ⟨L1, hL1⟩ := hne
  obtain ⟨hXL1, hL1π, hL1d⟩ := mem_ext.mp hL1
  rw [X.2] at hL1d
  -- a long line `L0`
  obtain ⟨L0, hL0π, hL0d, hL0⟩ : ∃ L0 : Submodule K (Fin N → K), L0 ≤ π ∧
      Module.finrank K L0 = 2 ∧ Fintype.card K - 1 ≤ wt L0 c := by
    have long : ∀ M : Submodule K (Fin N → K), M ≤ π → Module.finrank K M = 2 → 4 ≤ wt M c →
        Fintype.card K - 1 ≤ wt M c := by
      intro M hMπ hMd hM4
      rcases A_lines p a hG hD hc hw (hMπ.trans hπU) hMd with h | h
      · omega
      · exact h
    by_cases h4 : 4 ≤ wt L1 c
    · exact ⟨L1, hL1π, hL1d, long L1 hL1π hL1d h4⟩
    · obtain ⟨M, hMπ, hMd, -, -, hM4⟩ := other_line hπ hL1π hL1d hXL1 hcX (by omega)
      exact ⟨M, hMπ, hMd, long M hMπ hMd hM4⟩
  have ht := tele' (c := c) hL0π hL0d (Fintype.card K - 1) hL0 (fun P hPL hcP => by
    by_cases hbig : wt L0 c + 2 * Fintype.card K < wt π c
    · obtain ⟨M, hMπ, hMd, hML, hPM, hM4⟩ := other_line hπ hL0π hL0d hPL hcP hbig
      refine ⟨M, hMπ, hMd, hML, hPM, ?_⟩
      rcases A_lines p a hG hD hc hw (hMπ.trans hπU) hMd with h | h
      · omega
      · exact h
    · exfalso
      have := Finset.card_le_card (fun ℓ (hℓ : ℓ ∈ supp L0 c) => (mem_pts.mpr (mem_supp.mp hℓ).1))
      rw [← wt_eq, pts_card, hL0d, th_two] at this
      omega)
  apply Nat.div_le_of_le_mul
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card K = r + 37 := ⟨Fintype.card K - 37, by omega⟩
  rw [hr] at ht hL0 ⊢
  rw [show r + 37 - 1 = r + 36 by omega] at ht hL0 ⊢
  rw [show r + 36 - 1 = r + 35 by omega] at ht
  nlinarith

end ProxGapTight.Dev.Q366.PartA
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
alias O_heavy := ProxGapTight.Dev.Q366.PartA.O_heavy

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366.PartG
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ### Numerics -/
lemma th_zero (q : ℕ) : th q 0 = 0 := by simp [th]

lemma th_succ (q k : ℕ) : th q (k + 1) = q * th q k + 1 := by
  unfold th
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_succ, pow_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma th_one (q : ℕ) : th q 1 = 1 := by simp [th]

lemma th_two (q : ℕ) : th q 2 = q + 1 := by rw [th_succ, th_one]; ring

lemma th_three (q : ℕ) : th q 3 = q * q + q + 1 := by rw [th_succ, th_two]; ring

lemma pow_th (q k : ℕ) : ((q : ℤ) ^ k) = ((q : ℤ) - 1) * (th q k : ℤ) + 1 := by
  induction k with
  | zero => simp [th_zero]
  | succ k ih => rw [th_succ, pow_succ, ih]; push_cast; ring

lemma Wb_int (q n : ℕ) (hq : 2 ≤ q) (hn : 3 ≤ n) :
    (Wb q n : ℤ) = 3 * ((q : ℤ) - 1) * (((q : ℤ) - 1) * (th q (n - 3) : ℤ) + 1) - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : m + 3 - 2 = m + 1 := by omega
  have e2 : m + 3 - 3 = m := by omega
  have hu : 1 ≤ q ^ m := Nat.one_le_pow _ _ (by omega)
  have hle : 3 * q ^ m + 1 ≤ 3 * (q ^ m * q) := by nlinarith
  have hW : Wb q (m + 3) + 1 + 3 * q ^ m = 3 * (q ^ m * q) := by
    unfold Wb; rw [e1, e2, pow_succ]; omega
  have h := congrArg (fun x : ℕ => (x : ℤ)) hW
  push_cast at h
  rw [e2]
  have hp := pow_th q m
  linear_combination h + 3 * ((q : ℤ) - 1) * hp

lemma th_pos (q k : ℕ) (hk : 1 ≤ k) : 1 ≤ th q k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [th_succ]; omega

lemma q_ge (p a : ℕ) [hp : Fact p.Prime] (hG : Good p a K) : 37 ≤ Fintype.card K := by
  obtain ⟨hq, h32, h49, h121⟩ := hG
  rw [hq]
  have key : ∀ r : ℕ, r.Prime → r ∣ p ^ a → r = p := fun r hr hd =>
    (Nat.prime_dvd_prime_iff_eq hr hp.out).mp (hr.dvd_of_dvd_pow hd)
  by_contra hlt
  have h4 : p ^ a = 33 ∨ p ^ a = 34 ∨ p ^ a = 35 ∨ p ^ a = 36 := by omega
  rcases h4 with h | h | h | h
  · have e1 := key 3 (by norm_num) (by rw [h]; norm_num)
    have e2 := key 11 (by norm_num) (by rw [h]; norm_num)
    omega
  · have e1 := key 2 (by norm_num) (by rw [h]; norm_num)
    have e2 := key 17 (by norm_num) (by rw [h]; norm_num)
    omega
  · have e1 := key 5 (by norm_num) (by rw [h]; norm_num)
    have e2 := key 7 (by norm_num) (by rw [h]; norm_num)
    omega
  · have e1 := key 2 (by norm_num) (by rw [h]; norm_num)
    have e2 := key 3 (by norm_num) (by rw [h]; norm_num)
    omega

lemma numA (q x w S : ℤ) (hq : 37 ≤ q) (hx : 0 ≤ x) (z1 : w + (q * x + 1) * 3 = 3 + S)
    (z2 : (q * x + 1) * (3 * q - 2) ≤ S) (z3 : w ≤ 3 * (q - 1) * ((q - 1) * x + 1) - 1) : False := by
  nlinarith [mul_nonneg hx (by linarith : (0 : ℤ) ≤ q - 3)]

lemma numSolid (q B h h' wS : ℤ) (hq : 37 ≤ q) (hB2 : q * (q - 1) ≤ 2 * B + 1) (hB0 : 0 ≤ B)
    (z1 : B ≤ (q + 1) * h' + 3 * (q + 1 - h')) (z2 : h * B ≤ wS + 3 * q) (z3 : h' ≤ h)
    (_h'0 : 0 ≤ h') : 4 * q * q + q + 1 ≤ wS := by
  have hh2 : q - 5 ≤ 2 * h := by
    by_contra hcon
    push Not at hcon
    have : (q - 2) * (2 * h') ≤ (q - 2) * (q - 6) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    nlinarith
  have hhB : (q - 5) * (q * (q - 1) - 1) ≤ 4 * (h * B) := by
    have e1 : (q - 5) * (2 * B) ≤ (2 * h) * (2 * B) :=
      mul_le_mul_of_nonneg_right hh2 (by linarith)
    have e2 : (q - 5) * (q * (q - 1) - 1) ≤ (q - 5) * (2 * B) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℤ) ≤ q) (by linarith : (0 : ℤ) ≤ q))
        (by linarith : (0 : ℤ) ≤ q - 37)]

/-! ### Basic facts about the blueprint definitions -/
lemma mem_ext {T U V : Submodule K (Fin N → K)} :
    V ∈ ProxGapTight.Dev.Q366.ext T U ↔
      T ≤ V ∧ V ≤ U ∧ Module.finrank K V = Module.finrank K T + 1 := by
  simp [ProxGapTight.Dev.Q366.ext]

lemma mem_hyps {T U V : Submodule K (Fin N → K)} :
    V ∈ hyps T U ↔ IsHyp V U ∧ T ≤ V := by
  simp [hyps]

lemma mem_pts {U : Submodule K (Fin N → K)} {ℓ : Lines K N} : ℓ ∈ pts U ↔ ℓ.1 ≤ U := by
  simp [pts]

lemma res_of_le {p : ℕ} {T : Submodule K (Fin N → K)} {c : Lines K N → ZMod p} {ℓ : Lines K N}
    (h : ℓ.1 ≤ T) : res T c ℓ = c ℓ := by
  simp [res, h]

lemma sum_res {p : ℕ} {t τ : Submodule K (Fin N → K)} (h : t ≤ τ) (c : Lines K N → ZMod p) :
    ∑ ℓ ∈ pts t, res τ c ℓ = ∑ ℓ ∈ pts t, c ℓ := by
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  exact res_of_le (le_trans (mem_pts.mp hℓ) h)

lemma wt_le {p : ℕ} (U : Submodule K (Fin N → K)) (c : Lines K N → ZMod p) :
    wt U c ≤ th (Fintype.card K) (Module.finrank K U) := by
  rw [← pts_card]
  unfold wt
  exact Finset.card_filter_le _ _

lemma wt_mono {p : ℕ} {T U : Submodule K (Fin N → K)} (h : T ≤ U) (c : Lines K N → ZMod p) :
    wt T c ≤ wt U c := by
  unfold wt
  apply Finset.card_le_card
  intro ℓ hℓ
  rw [Finset.mem_filter, mem_pts] at hℓ ⊢
  exact ⟨le_trans hℓ.1 h, hℓ.2⟩

lemma exists_supp {p : ℕ} {T : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
    (h : 0 < wt T c) : ∃ Q : Lines K N, Q.1 ≤ T ∧ c Q ≠ 0 := by
  unfold wt at h
  obtain ⟨Q, hQ⟩ := Finset.card_pos.mp h
  rw [Finset.mem_filter, mem_pts] at hQ
  exact ⟨Q, hQ.1, hQ.2⟩

lemma inf_lt {A B : Submodule K (Fin N → K)} (hAB : A ≠ B)
    (h : Module.finrank K A = Module.finrank K B) :
    Module.finrank K (A ⊓ B : Submodule K (Fin N → K)) < Module.finrank K A := by
  by_contra hc
  push Not at hc
  have e1 : A ⊓ B = A := Submodule.eq_of_le_of_finrank_le inf_le_left hc
  have e2 : A ⊓ B = B := Submodule.eq_of_le_of_finrank_le inf_le_right (h ▸ hc)
  exact hAB (e1.symm.trans e2)

lemma line_eq {ℓ ℓ' : Lines K N} {M : Submodule K (Fin N → K)} (h : ℓ.1 ≤ M) (h' : ℓ'.1 ≤ M)
    (hM : Module.finrank K M ≤ 1) : ℓ = ℓ' := by
  have e1 : ℓ.1 = M := Submodule.eq_of_le_of_finrank_le h (by rw [ℓ.2]; exact hM)
  have e2 : ℓ'.1 = M := Submodule.eq_of_le_of_finrank_le h' (by rw [ℓ'.2]; exact hM)
  exact Subtype.ext (e1.trans e2.symm)

/-- the partition of the points of `U` by the planes through the 3-secant `t` -/
lemma tpartN {p : ℕ} {U t : Submodule K (Fin N → K)} (htU : t ≤ U)
    (ht : Module.finrank K t = 2) {c : Lines K N → ZMod p} (h3 : wt t c = 3) :
    wt U c + th (Fintype.card K) (Module.finrank K U - 2) * 3 =
      3 + ∑ τ ∈ ProxGapTight.Dev.Q366.ext t U, wt τ c := by
  have h := ext_partition htU c
  rw [ext_card htU, h3, ht] at h
  exact h

/-- what the planar stubs say about a plane through the 3-secant `t` -/
lemma plane_data (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    {c : Lines K N → ZMod p} (hc : c ∈ Code p U) {t : Submodule K (Fin N → K)}
    (ht : Module.finrank K t = 2) (h3 : wt t c = 3) {τ : Submodule K (Fin N → K)}
    (hτ : τ ∈ ProxGapTight.Dev.Q366.ext t U) :
    3 * Fintype.card K - 3 ≤ wt τ c ∧
    (wt τ c ≤ 4 * Fintype.card K - 22 →
    (wt τ c = 3 * Fintype.card K - 3 → p = 2 ∨ (a = 1 ∧ ∑ ℓ ∈ pts t, c ℓ = 0)) ∧
    (p = 2 → wt τ c ≠ 3 * Fintype.card K - 2 ∧ wt τ c ≠ 3 * Fintype.card K - 1 ∧
      wt τ c ≠ 3 * Fintype.card K) ∧
    (a = 1 → p ≠ 2 → ∑ ℓ ∈ pts t, c ℓ = 0 →
      wt τ c = 3 * Fintype.card K - 3 ∨ wt τ c = 3 * Fintype.card K) ∧
    (a = 1 → ∑ ℓ ∈ pts t, c ℓ ≠ 0 → 3 * Fintype.card K - 2 ≤ wt τ c)) := by
  obtain ⟨htτ, hτU, hτd⟩ := mem_ext.mp hτ
  have hτ3 : Module.finrank K τ = 3 := by rw [hτd, ht]
  have hres := res_mem p a hG hc hτU (by omega)
  have hwτ : wt τ (res τ c) = wt τ c := wt_res τ τ le_rfl c
  have hwt : wt t (res τ c) = 3 := by rw [wt_res t τ htτ]; exact h3
  have hs := sum_res htτ c
  refine ⟨?_, fun hl => ?_⟩
  · have := P3a p a hG hτ3 hres htτ ht hwt
    rwa [hwτ] at this
  · have := P3 p a hG hτ3 hres (by rwa [hwτ]) htτ ht hwt
    rwa [hwτ, hs] at this

/-! ### The r-argument: four dimensions, every plane through `t` tight -/
lemma r_arg (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hU : Module.finrank K U = 4) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    {t : Submodule K (Fin N → K)} (htU : t ≤ U) (ht : Module.finrank K t = 2) (h3 : wt t c = 3)
    (hall : ∀ τ ∈ ProxGapTight.Dev.Q366.ext t U, wt τ c = 3 * Fintype.card K - 3) : False := by
  have hq := q_ge p a hG
  obtain ⟨Q, hQt, hcQ⟩ := exists_supp (c := c) (T := t) (by omega)
  have hne : (ProxGapTight.Dev.Q366.ext t U).Nonempty := by
    rw [← Finset.card_pos, ext_card htU, hU, ht]
    rw [show 4 - 2 = 2 from rfl, th_two]; omega
  obtain ⟨τ0, hτ0⟩ := hne
  obtain ⟨htτ0, hτ0U, hτ0d⟩ := mem_ext.mp hτ0
  have hτ03 : Module.finrank K τ0 = 3 := by rw [hτ0d, ht]
  have hres0 := res_mem p a hG hc hτ0U (by omega)
  have P4τ0 := P4 p a hG hτ03 hres0 (by rw [wt_res τ0 τ0 le_rfl]; exact hall τ0 hτ0) htτ0 ht
    (by rw [wt_res t τ0 htτ0]; exact h3) hQt (by rw [res_of_le (le_trans hQt htτ0)]; exact hcQ)
  obtain ⟨r, hrτ0, hr2, hQr, -, hwr⟩ := P4τ0.2
  rw [wt_res r τ0 hrτ0] at hwr
  have hrU : r ≤ U := le_trans hrτ0 hτ0U
  have hbig : ∀ ρ ∈ ProxGapTight.Dev.Q366.ext r U, 3 * Fintype.card K - 3 ≤ wt ρ c := by
    intro ρ hρ
    obtain ⟨hrρ, hρU, hρd⟩ := mem_ext.mp hρ
    have hρ3 : Module.finrank K ρ = 3 := by rw [hρd, hr2]
    by_contra hlt
    push Not at hlt
    have hresρ := res_mem p a hG hc hρU (by omega)
    have h2c := P1 p a hG hρ3 hresρ (by rw [wt_res ρ ρ le_rfl]; omega)
    obtain ⟨s, hsρ, hQs, hws⟩ := twoComb_long h2c (by omega) (le_trans hQr hrρ)
      (by rw [res_of_le (le_trans hQr hrρ)]; exact hcQ)
    rw [wt_res s ρ hsρ.1, hρ3] at hws
    have hs2 : Module.finrank K s = 2 := by have := hsρ.2; omega
    have hws' : Fintype.card K ≤ wt s c := by simpa using hws
    have hst : t ≠ s := by rintro rfl; omega
    have hinf : Module.finrank K (t ⊓ s : Submodule K (Fin N → K)) = 1 := by
      have h1 := inf_lt hst (by rw [ht, hs2])
      have h2 : Module.finrank K Q.1 ≤ Module.finrank K (t ⊓ s : Submodule K (Fin N → K)) :=
        Submodule.finrank_mono (le_inf hQt hQs)
      rw [Q.2] at h2
      omega
    have hsup : Module.finrank K (t ⊔ s : Submodule K (Fin N → K)) = 3 := by
      have := Submodule.finrank_sup_add_finrank_inf_eq t s
      omega
    have hsU : s ≤ U := le_trans hsρ.1 hρU
    have hmem : t ⊔ s ∈ ProxGapTight.Dev.Q366.ext t U :=
      mem_ext.mpr ⟨le_sup_left, sup_le htU hsU, by rw [hsup, ht]⟩
    have hres' := res_mem p a hG hc (sup_le htU hsU) (by omega)
    have P4' := P4 p a hG hsup hres' (by rw [wt_res _ _ le_rfl]; exact hall _ hmem) le_sup_left ht
      (by rw [wt_res t _ le_sup_left]; exact h3) hQt
      (by rw [res_of_le (le_trans hQt le_sup_left)]; exact hcQ)
    have := P4'.1 s le_sup_right hs2 hQs
    rw [wt_res s _ le_sup_right] at this
    omega
  have hr := ext_partition hrU c
  rw [ext_card hrU, hU, hr2] at hr
  have hsum := Finset.card_nsmul_le_sum _ _ _ hbig
  rw [ext_card hrU, hU, hr2, smul_eq_mul] at hsum
  have hT := tpartN htU ht h3
  rw [Finset.sum_const_nat hall, ext_card htU, hU, ht] at hT
  rw [show 4 - 2 = 2 from rfl, th_two] at hr hsum hT
  obtain ⟨B3, hB3⟩ : ∃ B3, 3 * Fintype.card K - 3 = B3 := ⟨_, rfl⟩
  have hB3' : B3 + 3 = 3 * Fintype.card K := by omega
  rw [hB3] at hsum hT
  have : (Fintype.card K + 1) * wt r c ≤ (Fintype.card K + 1) * 2 :=
    Nat.mul_le_mul_left _ hwr
  nlinarith

/-! ### Dimension four -/
lemma D4 (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hU : Module.finrank K U = 4) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    {t : Submodule K (Fin N → K)} (htU : t ≤ U) (ht : Module.finrank K t = 2) (h3 : wt t c = 3)
    (j : ℕ)
    (hw : wt U c + 3 * Fintype.card K < 3 * Fintype.card K * Fintype.card K + j)
    (hcls : ∀ τ ∈ ProxGapTight.Dev.Q366.ext t U,
      wt τ c = 3 * Fintype.card K - 3 ∨ 3 * Fintype.card K + j ≤ wt τ c) : False := by
  have hq := q_ge p a hG
  by_cases hall : ∀ τ ∈ ProxGapTight.Dev.Q366.ext t U, wt τ c = 3 * Fintype.card K - 3
  · exact r_arg p a hG hU hc htU ht h3 hall
  push Not at hall
  obtain ⟨τ0, hτ0, hne⟩ := hall
  have hτ0' : 3 * Fintype.card K + j ≤ wt τ0 c := (hcls τ0 hτ0).resolve_left hne
  have hT := tpartN htU ht h3
  rw [← Finset.add_sum_erase _ _ hτ0] at hT
  have hrest := Finset.card_nsmul_le_sum ((ProxGapTight.Dev.Q366.ext t U).erase τ0)
    (fun τ => wt τ c) (3 * Fintype.card K - 3)
    (fun τ hτ => (plane_data p a hG hc ht h3 (Finset.mem_of_mem_erase hτ)).1)
  rw [Finset.card_erase_of_mem hτ0, ext_card htU, hU, ht, smul_eq_mul] at hrest
  rw [hU] at hT
  rw [show 4 - 2 = 2 from rfl, th_two] at hrest hT
  rw [show Fintype.card K + 1 - 1 = Fintype.card K by omega] at hrest
  obtain ⟨B3, hB3⟩ : ∃ B3, 3 * Fintype.card K - 3 = B3 := ⟨_, rfl⟩
  have hB3' : B3 + 3 = 3 * Fintype.card K := by omega
  rw [hB3] at hrest
  nlinarith

/-! ### Planes through a 3-secant inside a solid, and the OEX argument -/
lemma heavy_count (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hD : 4 ≤ Module.finrank K U) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (hw : wt U c ≤ Wb (Fintype.card K) (Module.finrank K U))
    {S : Submodule K (Fin N → K)} (hSU : S ≤ U) (hS4 : Module.finrank K S = 4)
    {s : Submodule K (Fin N → K)} (hsS : s ≤ S) (hs2 : Module.finrank K s = 2)
    (hs3 : wt s c = 3) :
    ((ProxGapTight.Dev.Q366.ext s S).filter
        (fun ρ => 4 * Fintype.card K - 21 ≤ wt ρ c)).card *
      (Fintype.card K * (Fintype.card K - 1) / 2) ≤ wt S c + 3 * Fintype.card K := by
  have hT := tpartN hsS hs2 hs3
  rw [hS4, show 4 - 2 = 2 from rfl, th_two] at hT
  have h1 : ∑ ρ ∈ (ProxGapTight.Dev.Q366.ext s S).filter
      (fun ρ => 4 * Fintype.card K - 21 ≤ wt ρ c), wt ρ c ≤
      ∑ ρ ∈ ProxGapTight.Dev.Q366.ext s S, wt ρ c :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have h2 := Finset.card_nsmul_le_sum ((ProxGapTight.Dev.Q366.ext s S).filter
      (fun ρ => 4 * Fintype.card K - 21 ≤ wt ρ c)) (fun ρ => wt ρ c)
      (Fintype.card K * (Fintype.card K - 1) / 2) (by
        intro ρ hρ
        rw [Finset.mem_filter] at hρ
        obtain ⟨hsρ, hρS, hρd⟩ := mem_ext.mp hρ.1
        exact O_heavy p a hG hD hc hw (le_trans hρS hSU) (by rw [hρd, hs2]) hρ.2)
  rw [smul_eq_mul] at h2
  omega

lemma half_bound (q : ℕ) (hq : 1 ≤ q) :
    (q : ℤ) * ((q : ℤ) - 1) ≤ 2 * ((q * (q - 1) / 2 : ℕ) : ℤ) + 1 := by
  have h1 := Nat.div_add_mod (q * (q - 1)) 2
  have h2 := Nat.mod_lt (q * (q - 1)) (by norm_num : 2 > 0)
  have h3 : ((q * (q - 1) : ℕ) : ℤ) = (q : ℤ) * ((q : ℤ) - 1) := by
    push_cast [Nat.cast_sub hq]; ring
  have h4 := congrArg (fun x : ℕ => (x : ℤ)) h1
  push_cast at h4
  rw [← h3]
  have h5 : ((q * (q - 1) % 2 : ℕ) : ℤ) ≤ 1 := by exact_mod_cast (by omega : q * (q - 1) % 2 ≤ 1)
  push_cast at h5 ⊢
  linarith

lemma solid (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hD : 4 ≤ Module.finrank K U) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (hw : wt U c ≤ Wb (Fintype.card K) (Module.finrank K U))
    {t : Submodule K (Fin N → K)} (ht : Module.finrank K t = 2) (h3 : wt t c = 3)
    {σ0 : Submodule K (Fin N → K)} (htσ : t ≤ σ0) (hσ3 : Module.finrank K σ0 = 3)
    (hheavy : 4 * Fintype.card K - 21 ≤ wt σ0 c)
    {S : Submodule K (Fin N → K)} (hS : S ∈ ProxGapTight.Dev.Q366.ext σ0 U) :
    4 * Fintype.card K * Fintype.card K + Fintype.card K + 1 ≤ wt S c := by
  have hq := q_ge p a hG
  obtain ⟨hσS, hSU, hSd⟩ := mem_ext.mp hS
  have hS4 : Module.finrank K S = 4 := by rw [hSd, hσ3]
  have htS := le_trans htσ hσS
  have hB := O_heavy p a hG hD hc hw (le_trans hσS hSU) hσ3 hheavy
  have hB2 := half_bound (Fintype.card K) (by omega)
  set B := Fintype.card K * (Fintype.card K - 1) / 2 with hBdef
  set q := Fintype.card K with hqdef
  by_cases hlight : ∃ π ∈ ProxGapTight.Dev.Q366.ext t S, wt π c ≤ 4 * q - 22
  · obtain ⟨π, hπ, hπl⟩ := hlight
    obtain ⟨htπ, hπS, hπd⟩ := mem_ext.mp hπ
    have hπ3 : Module.finrank K π = 3 := by rw [hπd, ht]
    have hπU := le_trans hπS hSU
    have hres := res_mem p a hG hc hπU (by omega)
    obtain ⟨⟨H, hHt, hH0, t', ht'π, ht'2, hHt', ht't, ht'3⟩, -⟩ := P5 p a hG hπ3 hres
      (by rw [wt_res π π le_rfl]; exact hπl) htπ ht (by rw [wt_res t π htπ]; exact h3)
    rw [res_of_le (le_trans hHt htπ)] at hH0
    rw [wt_res t' π ht'π] at ht'3
    have hπσ : π ≠ σ0 := by rintro rfl; omega
    have ht'σ : ¬ t' ≤ σ0 := by
      intro h
      have hlt := inf_lt hπσ (by rw [hπ3, hσ3])
      have e : t = π ⊓ σ0 := Submodule.eq_of_le_of_finrank_le (le_inf htπ htσ) (by rw [ht]; omega)
      have h' : t' ≤ t := e ▸ le_inf ht'π h
      exact ht't (Submodule.eq_of_le_of_finrank_le h' (by rw [ht, ht'2]))
    have hmeet : Module.finrank K (σ0 ⊓ t' : Submodule K (Fin N → K)) ≤ 1 := by
      have h1 : Module.finrank K (σ0 ⊓ t' : Submodule K (Fin N → K)) ≤ Module.finrank K t' :=
        Submodule.finrank_mono inf_le_right
      by_contra h2
      have : σ0 ⊓ t' = t' := Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
      exact ht'σ (this ▸ inf_le_left)
    have ht'S : t' ≤ S := le_trans ht'π hπS
    have hjoin : ∀ L ∈ ProxGapTight.Dev.Q366.ext H.1 σ0,
        t' ⊔ L ∈ ProxGapTight.Dev.Q366.ext t' S := by
      intro L hL
      obtain ⟨hHL, hLσ, hLd⟩ := mem_ext.mp hL
      rw [H.2] at hLd
      have hi : Module.finrank K (t' ⊓ L : Submodule K (Fin N → K)) = 1 := by
        have h1 : Module.finrank K (t' ⊓ L : Submodule K (Fin N → K)) ≤
            Module.finrank K (σ0 ⊓ t' : Submodule K (Fin N → K)) :=
          Submodule.finrank_mono (le_inf (le_trans inf_le_right hLσ) inf_le_left)
        have h2 : Module.finrank K H.1 ≤ Module.finrank K (t' ⊓ L : Submodule K (Fin N → K)) :=
          Submodule.finrank_mono (le_inf hHt' hHL)
        rw [H.2] at h2
        omega
      have := Submodule.finrank_sup_add_finrank_inf_eq t' L
      exact mem_ext.mpr ⟨le_sup_left, sup_le ht'S (le_trans hLσ hσS), by omega⟩
    have hinj : Set.InjOn (fun L => t' ⊔ L)
        (↑((ProxGapTight.Dev.Q366.ext H.1 σ0).filter (fun L => 4 ≤ wt L c)) :
          Set (Submodule K (Fin N → K))) := by
      intro L1 hL1 L2 hL2 heq
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hL1 hL2 heq
      obtain ⟨-, hL1σ, hL1d⟩ := mem_ext.mp hL1.1
      obtain ⟨-, hL2σ, hL2d⟩ := mem_ext.mp hL2.1
      have hρ3 : Module.finrank K (t' ⊔ L1 : Submodule K (Fin N → K)) = 3 := by
        rw [(mem_ext.mp (hjoin L1 hL1.1)).2.2, ht'2]
      have hρσ : t' ⊔ L1 ≠ σ0 := fun h => ht'σ (h ▸ le_sup_left)
      have hlt := inf_lt hρσ (by rw [hρ3, hσ3])
      rw [hρ3] at hlt
      rw [H.2] at hL1d hL2d
      have e1 : L1 = (t' ⊔ L1) ⊓ σ0 :=
        Submodule.eq_of_le_of_finrank_le (le_inf le_sup_right hL1σ) (by omega)
      have e2 : L2 = (t' ⊔ L1) ⊓ σ0 :=
        Submodule.eq_of_le_of_finrank_le (le_inf (heq ▸ le_sup_right) hL2σ) (by omega)
      rw [e1, e2]
    have hmaps : Set.MapsTo (fun L => t' ⊔ L)
        (↑((ProxGapTight.Dev.Q366.ext H.1 σ0).filter (fun L => 4 ≤ wt L c)) :
          Set (Submodule K (Fin N → K)))
        (↑((ProxGapTight.Dev.Q366.ext t' S).filter (fun ρ => 4 * q - 21 ≤ wt ρ c)) :
          Set (Submodule K (Fin N → K))) := by
      intro L hL
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hL ⊢
      refine ⟨hjoin L hL.1, ?_⟩
      by_contra hl
      push Not at hl
      obtain ⟨hHL, hLσ, hLd⟩ := mem_ext.mp hL.1
      obtain ⟨-, hρS, hρd⟩ := mem_ext.mp (hjoin L hL.1)
      have hρ3 : Module.finrank K (t' ⊔ L : Submodule K (Fin N → K)) = 3 := by rw [hρd, ht'2]
      have hresρ := res_mem p a hG hc (le_trans hρS hSU) (by omega)
      have h5 := (P5 p a hG hρ3 hresρ (by rw [wt_res _ _ le_rfl]; omega) le_sup_left ht'2
        (by rw [wt_res t' _ le_sup_left]; exact ht'3)).2
      obtain ⟨X, hXL, hXt', hcX⟩ := h5 L t' le_sup_right (by rw [hLd, H.2])
        (by rw [wt_res L _ le_sup_right]; exact hL.2) le_sup_left ht'2
        (by rw [wt_res t' _ le_sup_left]; exact ht'3)
      rw [res_of_le (le_trans hXL le_sup_right)] at hcX
      have hXH : X = H := line_eq (le_inf (le_trans hXL hLσ) hXt')
        (le_inf (le_trans hHt htσ) hHt') hmeet
      exact hcX (hXH ▸ hH0)
    have hcardle := Finset.card_le_card_of_injOn (fun L => t' ⊔ L) hmaps hinj
    have hcnt := heavy_count p a hG hD hc hw hSU hS4 ht'S ht'2 ht'3
    have hHσ : H.1 ≤ σ0 := le_trans hHt htσ
    have hpartH := ext_partition hHσ c
    have hcardH : (ProxGapTight.Dev.Q366.ext H.1 σ0).card = q + 1 := by
      rw [ext_card hHσ, H.2, hσ3, show 3 - 1 = 2 from rfl, th_two]
    rw [hcardH] at hpartH
    have hsplit := Finset.sum_filter_add_sum_filter_not (ProxGapTight.Dev.Q366.ext H.1 σ0)
      (fun L => 4 ≤ wt L c) (fun L => wt L c)
    have hb1 := Finset.sum_le_card_nsmul ((ProxGapTight.Dev.Q366.ext H.1 σ0).filter
      (fun L => 4 ≤ wt L c)) (fun L => wt L c) (q + 1) (by
        intro L hL
        rw [Finset.mem_filter] at hL
        obtain ⟨-, -, hLd⟩ := mem_ext.mp hL.1
        have := wt_le L c
        rw [hLd, H.2, show 1 + 1 = 2 from rfl, th_two] at this
        exact this)
    have hb2 := Finset.sum_le_card_nsmul ((ProxGapTight.Dev.Q366.ext H.1 σ0).filter
      (fun L => ¬ 4 ≤ wt L c)) (fun L => wt L c) 3 (by
        intro L hL
        rw [Finset.mem_filter] at hL
        omega)
    have hcards := Finset.card_filter_add_card_filter_not (s := ProxGapTight.Dev.Q366.ext H.1 σ0)
      (fun L => 4 ≤ wt L c)
    rw [hcardH] at hcards
    rw [smul_eq_mul] at hb1 hb2
    set h' := ((ProxGapTight.Dev.Q366.ext H.1 σ0).filter (fun L => 4 ≤ wt L c)).card
    set h := ((ProxGapTight.Dev.Q366.ext t' S).filter (fun ρ => 4 * q - 21 ≤ wt ρ c)).card
    -- `B ≤ wt σ0 ≤ ∑ wt L ≤ (q+1) h' + 3 (q+1-h')`
    have hσle : wt σ0 c ≤ (q + 1) * h' + 3 * (q + 1 - h') := by
      have e : (q + 1 - h') = ((ProxGapTight.Dev.Q366.ext H.1 σ0).filter
          (fun L => ¬ 4 ≤ wt L c)).card := by omega
      rw [e]
      nlinarith
    have hh'le : h' ≤ q + 1 := by omega
    -- numerics in ℤ
    have z1 : (B : ℤ) ≤ (q + 1) * h' + 3 * (q + 1 - h') := by
      have := le_trans hB hσle
      zify [hh'le] at this
      linarith
    have z2 : (h : ℤ) * B ≤ wt S c + 3 * q := by exact_mod_cast hcnt
    have z3 : (h' : ℤ) ≤ h := by exact_mod_cast hcardle
    have hqz : (37 : ℤ) ≤ q := by exact_mod_cast hq
    have hB0 : (0 : ℤ) ≤ B := Int.natCast_nonneg _
    have : (4 * q * q + q + 1 : ℤ) ≤ wt S c :=
      numSolid q B h h' (wt S c) hqz hB2 hB0 z1 z2 z3 (Int.natCast_nonneg _)
    exact_mod_cast this
  · push Not at hlight
    have hcnt := heavy_count p a hG hD hc hw hSU hS4 htS ht h3
    have hf : (ProxGapTight.Dev.Q366.ext t S).filter (fun ρ => 4 * q - 21 ≤ wt ρ c) =
        ProxGapTight.Dev.Q366.ext t S :=
      Finset.filter_true_of_mem (fun π hπ => by have := hlight π hπ; omega)
    rw [hf, ext_card htS, hS4, ht, show 4 - 2 = 2 from rfl, th_two] at hcnt
    have z2 : ((q : ℤ) + 1) * B ≤ wt S c + 3 * q := by exact_mod_cast hcnt
    have hqz : (37 : ℤ) ≤ q := by exact_mod_cast hq
    have : (4 * q * q + q + 1 : ℤ) ≤ wt S c := by
      nlinarith [mul_le_mul_of_nonneg_left hB2 (by linarith : (0 : ℤ) ≤ q + 1),
        mul_nonneg (mul_nonneg (by linarith : (0 : ℤ) ≤ q) (by linarith : (0 : ℤ) ≤ q))
        (by linarith : (0 : ℤ) ≤ q - 37)]
    exact_mod_cast this

/-- OEX: when `wt U c ≤ Wb`, no plane through the 3-secant `t` is heavy -/
lemma OEX (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hD : 4 ≤ Module.finrank K U) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (hw : wt U c ≤ Wb (Fintype.card K) (Module.finrank K U))
    {t : Submodule K (Fin N → K)} (ht : Module.finrank K t = 2) (h3 : wt t c = 3)
    {σ0 : Submodule K (Fin N → K)} (hσ0 : σ0 ∈ ProxGapTight.Dev.Q366.ext t U)
    (hheavy : 4 * Fintype.card K - 21 ≤ wt σ0 c) : False := by
  have hq := q_ge p a hG
  obtain ⟨htσ, hσU, hσd⟩ := mem_ext.mp hσ0
  have hσ3 : Module.finrank K σ0 = 3 := by rw [hσd, ht]
  have hsolid := fun S (hS : S ∈ ProxGapTight.Dev.Q366.ext σ0 U) =>
    solid p a hG hD hc hw ht h3 htσ hσ3 hheavy hS
  have hpart := ext_partition hσU c
  rw [ext_card hσU, hσ3] at hpart
  have hlow := Finset.card_nsmul_le_sum _ _ _ hsolid
  rw [ext_card hσU, hσ3, smul_eq_mul] at hlow
  have hs0 := wt_le σ0 c
  rw [hσ3, th_three] at hs0
  have hWb := Wb_int (Fintype.card K) (Module.finrank K U) (by omega) (by omega)
  have hx := th_pos (Fintype.card K) (Module.finrank K U - 3) (by omega)
  set x := th (Fintype.card K) (Module.finrank K U - 3)
  set q := Fintype.card K
  have z1 : (wt U c : ℤ) + x * wt σ0 c = wt σ0 c + ∑ S ∈ ProxGapTight.Dev.Q366.ext σ0 U,
      (wt S c : ℤ) := by exact_mod_cast hpart
  have z2 : (x : ℤ) * (4 * q * q + q + 1) ≤ ∑ S ∈ ProxGapTight.Dev.Q366.ext σ0 U,
      (wt S c : ℤ) := by exact_mod_cast hlow
  have z3 : (wt σ0 c : ℤ) ≤ q * q + q + 1 := by exact_mod_cast hs0
  have z4 : (wt U c : ℤ) ≤ Wb q (Module.finrank K U) := by exact_mod_cast hw
  have hxz : (1 : ℤ) ≤ x := by exact_mod_cast hx
  have hqz : (37 : ℤ) ≤ q := by exact_mod_cast hq
  rw [hWb] at z4
  nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ x - 1) (by linarith : (0 : ℤ) ≤ q * q + q + 1 - wt σ0 c),
    mul_nonneg (by linarith : (0 : ℤ) ≤ x - 1) (by linarith : (0 : ℤ) ≤ q)]

/-! ### The induction -/
/-- hyperplane averaging: the planes facts transported to a hyperplane through `t` -/
lemma hyp_bound (p : ℕ) {U : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
    {t : Submodule K (Fin N → K)} (htU : t ≤ U) (ht : Module.finrank K t = 2) (h3 : wt t c = 3)
    (hlt : 2 < Module.finrank K U) (m : ℕ) (hm : ∀ P ∈ hyps t U, m ≤ wt P c) :
    th (Fintype.card K) (Module.finrank K U - 2) * m ≤
      th (Fintype.card K) (Module.finrank K U - 2) * 3 +
      th (Fintype.card K) (Module.finrank K U - 2 - 1) * (wt U c - 3) := by
  have hs := hyps_sum htU (by omega) c
  have hlow := Finset.card_nsmul_le_sum _ _ _ hm
  rw [smul_eq_mul] at hlow
  rw [hyps_card htU, ht] at hs hlow
  rw [h3] at hs
  omega

theorem G_core (p a : ℕ) [Fact p.Prime] (hG : Good p a K) (n : ℕ) (hn : 3 ≤ n) :
    ∀ U : Submodule K (Fin N → K), Module.finrank K U = n → ∀ c ∈ Code p U,
    ∀ t : Submodule K (Fin N → K), t ≤ U → Module.finrank K t = 2 → wt t c = 3 →
    Wb (Fintype.card K) n < wt U c ∧ (p = 2 → 4 ≤ n → Wb (Fintype.card K) n + 1 < wt U c) := by
  have hq := q_ge p a hG
  induction n, hn using Nat.le_induction with
  | base =>
    intro U hU c hc t htU ht h3
    have h := P3a p a hG hU hc htU ht h3
    have hW := Wb_int (Fintype.card K) 3 (by omega) le_rfl
    simp only [show 3 - 3 = 0 from rfl, th_zero] at hW
    refine ⟨by omega, fun _ h4 => by omega⟩
  | succ n hn ih =>
    intro U hU c hc t htU ht h3
    have hpd := fun τ (hτ : τ ∈ ProxGapTight.Dev.Q366.ext t U) => plane_data p a hG hc ht h3 hτ
    have hT := tpartN htU ht h3
    rw [hU] at hT
    have hw3 : 3 ≤ wt U c := h3 ▸ wt_mono htU c
    -- hyperplanes through `t` inherit the induction hypothesis
    have hhypIH : ∀ P ∈ hyps t U, Wb (Fintype.card K) n < wt P c ∧
        (p = 2 → 4 ≤ n → Wb (Fintype.card K) n + 1 < wt P c) := by
      intro P hP
      obtain ⟨hPU, htP⟩ := mem_hyps.mp hP
      have hPd : Module.finrank K P = n := by have := hPU.2; omega
      have hres := res_mem p a hG hc hPU.1 (by omega)
      have := ih P hPd (res P c) hres t htP ht (by rw [wt_res t P htP]; exact h3)
      rwa [wt_res P P le_rfl] at this
    have hqz : (37 : ℤ) ≤ Fintype.card K := by exact_mod_cast hq
    have strong2 : p = 2 → Wb (Fintype.card K) (n + 1) + 1 < wt U c := by
      intro hp2
      by_contra hcon
      push Not at hcon
      rcases Nat.lt_or_ge n 4 with hn4 | hn4
      · have hn3 : n = 3 := by omega
        subst hn3
        refine D4 p a hG (by omega) hc htU ht h3 1 ?_ ?_
        · have hW := Wb_int (Fintype.card K) 4 (by omega) (by omega)
          rw [show 4 - 3 = 1 from rfl, th_one, Nat.cast_one, mul_one] at hW
          have : (wt U c : ℤ) ≤ Wb (Fintype.card K) 4 + 1 := by exact_mod_cast hcon
          have : (wt U c : ℤ) + 3 * Fintype.card K < 3 * Fintype.card K * Fintype.card K + 1 := by
            nlinarith
          exact_mod_cast this
        · intro τ hτ
          obtain ⟨h1, h2⟩ := hpd τ hτ
          by_cases hl : wt τ c ≤ 4 * Fintype.card K - 22
          · have := (h2 hl).2.1 hp2
            omega
          · omega
      · obtain ⟨r, rfl⟩ : ∃ r, n = r + 4 := ⟨n - 4, by omega⟩
        have hb := hyp_bound p htU ht h3 (by omega) (Wb (Fintype.card K) (r + 4) + 2)
          (fun P hP => (hhypIH P hP).2 hp2 (by omega))
        rw [hU, show r + 4 + 1 - 2 = r + 3 by omega, show r + 3 - 1 = r + 2 by omega] at hb
        have hWn := Wb_int (Fintype.card K) (r + 4) (by omega) (by omega)
        have hWm := Wb_int (Fintype.card K) (r + 4 + 1) (by omega) (by omega)
        rw [show r + 4 - 3 = r + 1 by omega] at hWn
        rw [show r + 4 + 1 - 3 = r + 2 by omega] at hWm
        have hk := th_succ (Fintype.card K) (r + 2)
        have hy := th_succ (Fintype.card K) (r + 1)
        have hz := th_pos (Fintype.card K) (r + 1) (by omega)
        set q := Fintype.card K
        set z := th q (r + 1)
        set y := th q (r + 2)
        set k := th q (r + 3)
        have zb : (k : ℤ) * ((Wb q (r + 4) : ℤ) + 2) ≤ k * 3 + y * ((wt U c : ℤ) - 3) := by
          have := hb
          zify [hw3] at this
          exact this
        have zw : (wt U c : ℤ) ≤ Wb q (r + 4 + 1) + 1 := by exact_mod_cast hcon
        have zk : (k : ℤ) = q * y + 1 := by exact_mod_cast hk
        have zy : (y : ℤ) = q * z + 1 := by exact_mod_cast hy
        have zz : (1 : ℤ) ≤ z := by exact_mod_cast hz
        rw [hWn] at zb
        rw [hWm] at zw
        have hpos : (0 : ℤ) < z * ((q : ℤ) ^ 2 - 3 * q + 3) + q - 2 := by nlinarith
        have hy0 : (0 : ℤ) ≤ y := by positivity
        rw [zk] at zb
        rw [zy] at zb zw hy0
        nlinarith [mul_le_mul_of_nonneg_left zw hy0]
    refine ⟨?_, fun hp2 _ => strong2 hp2⟩
    by_cases hp2 : p = 2
    · have := strong2 hp2
      omega
    by_contra hcon
    push Not at hcon
    by_cases hodd : a = 1 ∧ ∑ ℓ ∈ pts t, c ℓ = 0
    · obtain ⟨ha1, hσ⟩ := hodd
      have hcls3 : ∀ τ ∈ ProxGapTight.Dev.Q366.ext t U, wt τ c ≤ 4 * Fintype.card K - 22 →
          wt τ c = 3 * Fintype.card K - 3 ∨ wt τ c = 3 * Fintype.card K :=
        fun τ hτ hl => ((hpd τ hτ).2 hl).2.2.1 ha1 hp2 hσ
      rcases Nat.lt_or_ge n 4 with hn4 | hn4
      · have hn3 : n = 3 := by omega
        subst hn3
        refine D4 p a hG (by omega) hc htU ht h3 0 ?_ ?_
        · have hW := Wb_int (Fintype.card K) 4 (by omega) (by omega)
          rw [show 4 - 3 = 1 from rfl, th_one, Nat.cast_one, mul_one] at hW
          have : (wt U c : ℤ) ≤ Wb (Fintype.card K) 4 := by exact_mod_cast hcon
          have : (wt U c : ℤ) + 3 * Fintype.card K < 3 * Fintype.card K * Fintype.card K + 0 := by
            nlinarith
          exact_mod_cast this
        · intro τ hτ
          by_cases hl : wt τ c ≤ 4 * Fintype.card K - 22
          · have := hcls3 τ hτ hl
            omega
          · omega
      · obtain ⟨r, rfl⟩ : ∃ r, n = r + 4 := ⟨n - 4, by omega⟩
        -- no heavy plane through `t`
        have hlight : ∀ τ ∈ ProxGapTight.Dev.Q366.ext t U, wt τ c ≤ 4 * Fintype.card K - 22 := by
          intro τ hτ
          by_contra hh
          push Not at hh
          exact OEX p a hG (by omega) hc (by rw [hU]; exact hcon) ht h3 hτ (by omega)
        have hdvd : 3 ∣ ∑ τ ∈ ProxGapTight.Dev.Q366.ext t U, wt τ c := by
          apply Finset.dvd_sum
          intro τ hτ
          have := hcls3 τ hτ (hlight τ hτ)
          omega
        have h3w : 3 ∣ wt U c := by omega
        have hb := hyp_bound p htU ht h3 (by omega) (Wb (Fintype.card K) (r + 4) + 1)
          (fun P hP => (hhypIH P hP).1)
        rw [hU, show r + 4 + 1 - 2 = r + 3 by omega, show r + 3 - 1 = r + 2 by omega] at hb
        have hWn := Wb_int (Fintype.card K) (r + 4) (by omega) (by omega)
        have hWm := Wb_int (Fintype.card K) (r + 4 + 1) (by omega) (by omega)
        rw [show r + 4 - 3 = r + 1 by omega] at hWn
        rw [show r + 4 + 1 - 3 = r + 2 by omega] at hWm
        have hk := th_succ (Fintype.card K) (r + 2)
        have hy := th_succ (Fintype.card K) (r + 1)
        have hz := th_pos (Fintype.card K) (r + 1) (by omega)
        set q := Fintype.card K
        set z := th q (r + 1)
        set y := th q (r + 2)
        set k := th q (r + 3)
        have zb : (k : ℤ) * ((Wb q (r + 4) : ℤ) + 1) ≤ k * 3 + y * ((wt U c : ℤ) - 3) := by
          have := hb
          zify [hw3] at this
          exact this
        have zw0 : (wt U c : ℤ) ≤ Wb q (r + 4 + 1) := by exact_mod_cast hcon
        have h3wz : (3 : ℤ) ∣ (wt U c : ℤ) := by exact_mod_cast h3w
        have zw : (wt U c : ℤ) + 3 ≤ Wb q (r + 4 + 1) + 1 := by
          have hM : (Wb q (r + 4 + 1) : ℤ) + 1 =
              3 * (((q : ℤ) - 1) * (((q : ℤ) - 1) * (y : ℤ) + 1)) := by rw [hWm]; ring
          omega
        have zk : (k : ℤ) = q * y + 1 := by exact_mod_cast hk
        have zy : (y : ℤ) = q * z + 1 := by exact_mod_cast hy
        have zz : (1 : ℤ) ≤ z := by exact_mod_cast hz
        rw [hWn] at zb
        rw [hWm] at zw
        have hy0 : (0 : ℤ) ≤ y := by positivity
        rw [zk] at zb
        rw [zy] at zb zw hy0
        nlinarith [mul_le_mul_of_nonneg_left zw hy0]
    · -- every plane through `t` has weight at least `3q - 2`
      have hge : ∀ τ ∈ ProxGapTight.Dev.Q366.ext t U, 3 * Fintype.card K - 2 ≤ wt τ c := by
        intro τ hτ
        obtain ⟨h1, h2⟩ := hpd τ hτ
        by_contra hlt
        push Not at hlt
        have heq : wt τ c = 3 * Fintype.card K - 3 := by omega
        rcases (h2 (by omega)).1 heq with h | h
        · exact hp2 h
        · exact hodd h
      have hlow := Finset.card_nsmul_le_sum _ _ _ hge
      rw [ext_card htU, hU, ht, smul_eq_mul] at hlow
      have hW := Wb_int (Fintype.card K) (n + 1) (by omega) (by omega)
      have hk := th_succ (Fintype.card K) (n - 2)
      rw [show n - 2 + 1 = n + 1 - 2 by omega] at hk
      rw [show n + 1 - 3 = n - 2 by omega] at hW
      set q := Fintype.card K
      set x := th q (n - 2)
      set k := th q (n + 1 - 2)
      have z1 : (wt U c : ℤ) + k * 3 = 3 + ∑ τ ∈ ProxGapTight.Dev.Q366.ext t U, (wt τ c : ℤ) := by
        exact_mod_cast hT
      have z2 : (k : ℤ) * (3 * q - 2) ≤ ∑ τ ∈ ProxGapTight.Dev.Q366.ext t U, (wt τ c : ℤ) := by
        have := hlow
        zify [(by omega : 2 ≤ 3 * q)] at this
        exact_mod_cast this
      have z3 : (wt U c : ℤ) ≤ Wb q (n + 1) := by exact_mod_cast hcon
      have zk : (k : ℤ) = q * x + 1 := by exact_mod_cast hk
      have hx0 : (0 : ℤ) ≤ x := by positivity
      rw [hW] at z3
      rw [zk] at z1 z2
      exact numA q x (wt U c) _ hqz hx0 z1 z2 z3

theorem G_main (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hD : 3 ≤ Module.finrank K U) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    {t : Submodule K (Fin N → K)} (htU : t ≤ U) (ht : Module.finrank K t = 2) (h3 : wt t c = 3) :
    Wb (Fintype.card K) (Module.finrank K U) < wt U c :=
  (G_core p a hG (Module.finrank K U) hD U rfl c hc t htU ht h3).1

end ProxGapTight.Dev.Q366.PartG
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ## Part G: no 3-secant -/
alias G_main := ProxGapTight.Dev.Q366.PartG.G_main

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace ProxGapTight.Dev.Q366.PartA
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ### C: no `(Fintype.card K-1)`-secant -/
theorem C_lines (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hD : 4 ≤ Module.finrank K U) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (hw : wt U c ≤ Wb (Fintype.card K) (Module.finrank K U))
    {L : Submodule K (Fin N → K)} (hLU : L ≤ U) (hL : Module.finrank K L = 2) :
    wt L c ≠ Fintype.card K - 1 := by
  intro hq1
  have hq := q_ge p a hG
  refine planes_bound hD (by omega) hw hLU hL (3 * Fintype.card K - 3) le_rfl (fun τ hτ => ?_)
  obtain ⟨hLτ, hτU, hτd⟩ := mem_ext.mp hτ
  have hτ3 : Module.finrank K τ = 3 := by rw [hτd, hL]
  have hheavy : 4 * Fintype.card K - 21 ≤ wt τ c := by
    by_contra hlt
    have hr := res_mem p a hG hc hτU (by omega)
    obtain ⟨t, htτ, htd, ht3⟩ := P6 p a hG hτ3 hr (by rw [wt_res τ τ le_rfl c]; omega) hLτ hL
      (by rw [wt_res L τ hLτ c]; exact hq1)
    rw [wt_res t τ htτ c] at ht3
    have := G_main p a hG (by omega) hc (htτ.trans hτU) htd ht3
    omega
  have hO := O_heavy p a hG hD hc hw hτU hτ3 hheavy
  have e := Nat.div_mul_le_self (Fintype.card K * (Fintype.card K - 1)) 2
  have e2 : Fintype.card K * (Fintype.card K - 1) / 2 * 2 + 1 ≥ Fintype.card K * (Fintype.card K - 1) := by omega
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card K = r + 37 := ⟨Fintype.card K - 37, by omega⟩
  rw [hq1, hr]
  rw [hr, show r + 37 - 1 = r + 36 by omega] at e2 hO
  rw [show r + 37 - 1 = r + 36 by omega, show 3 * (r + 37) - 3 = 3 * r + 108 by omega]
  nlinarith

end ProxGapTight.Dev.Q366.PartA
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ## Part C: no (q-1)-secant -/
alias C_lines := ProxGapTight.Dev.Q366.PartA.C_lines

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace ProxGapTight.Dev.Q366.PartK
open ProxGapTight ProxGapTight.Dev.Q366
open Classical
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ### Numerics -/
lemma th_add (q a b : ℕ) : th q (a + b) = th q a + q ^ a * th q b := by
  unfold th
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]

lemma th_one (q : ℕ) : th q 1 = 1 := by simp [th]

lemma th_two (q : ℕ) : th q 2 = 1 + q := by simp [th, Finset.sum_range_succ]

lemma th_three (q : ℕ) : th q 3 = 1 + q + q * q := by
  simp [th, Finset.sum_range_succ]; ring

lemma th_succ_sub (q t : ℕ) : th q (t + 1) - th q t = q ^ t := by
  rw [th_add, th_one]
  omega

lemma th_lt_pow (q : ℕ) (hq : 2 ≤ q) (m : ℕ) : th q m < q ^ m := by
  induction m with
  | zero => simp [th]
  | succ n ih =>
    rw [th_add, th_one, pow_succ]
    nlinarith

lemma th_succ' (q m : ℕ) : q * th q m + 1 = th q m + q ^ m := by
  have h1 := th_add q 1 m
  have h2 := th_add q m 1
  rw [th_one, pow_one] at h1
  rw [th_one, mul_one, add_comm m 1, h1] at h2
  omega

/-! ### Points -/
lemma mem_pts (U : Submodule K (Fin N → K)) (ℓ : Lines K N) : ℓ ∈ pts U ↔ ℓ.1 ≤ U := by
  simp [pts]

lemma pts_mono {T U : Submodule K (Fin N → K)} (h : T ≤ U) : pts T ⊆ pts U := by
  intro ℓ hℓ
  rw [mem_pts] at hℓ ⊢
  exact hℓ.trans h

lemma card_pts_sdiff {T V : Submodule K (Fin N → K)} (h : T ≤ V) :
    (pts V \ pts T).card =
      th (Fintype.card K) (Module.finrank K V) - th (Fintype.card K) (Module.finrank K T) := by
  rw [Finset.card_sdiff_of_subset (pts_mono h), pts_card, pts_card]

lemma mem_hyps {T U V : Submodule K (Fin N → K)} :
    V ∈ hyps T U ↔ IsHyp V U ∧ T ≤ V := by
  simp [hyps]

lemma le_wt {p : ℕ} {V : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
    {S : Finset (Lines K N)} (hS : S ⊆ pts V) (hc : ∀ ℓ ∈ S, c ℓ ≠ 0) : S.card ≤ wt V c := by
  unfold wt
  apply Finset.card_le_card
  intro ℓ hℓ
  exact Finset.mem_filter.mpr ⟨hS hℓ, hc ℓ hℓ⟩

lemma wt_le {p : ℕ} (V : Submodule K (Fin N → K)) (c : Lines K N → ZMod p) :
    wt V c ≤ th (Fintype.card K) (Module.finrank K V) := by
  rw [← pts_card]
  unfold wt
  exact Finset.card_filter_le _ _

lemma wt_add_holes {p : ℕ} (V : Submodule K (Fin N → K)) (c : Lines K N → ZMod p) :
    wt V c + ((pts V).filter (fun ℓ => c ℓ = 0)).card =
      th (Fintype.card K) (Module.finrank K V) := by
  rw [← pts_card]
  unfold wt
  rw [← Finset.card_filter_add_card_filter_not (s := pts V) (fun ℓ => c ℓ ≠ 0)]
  simp only [ne_eq, not_not]

lemma pts_bot : pts (⊥ : Submodule K (Fin N → K)) = ∅ := by
  ext ℓ
  simp only [mem_pts, Finset.notMem_empty, iff_false, le_bot_iff]
  intro h
  have := ℓ.2
  rw [h, finrank_bot] at this
  exact zero_ne_one this

lemma wt_bot {p : ℕ} (c : Lines K N → ZMod p) : wt (⊥ : Submodule K (Fin N → K)) c = 0 := by
  unfold wt
  rw [pts_bot]
  rfl

/-! ### Geometry -/
lemma line_eq_of_le {ℓ ℓ' : Lines K N} (h : ℓ.1 ≤ ℓ'.1) : ℓ = ℓ' :=
  Subtype.ext (Submodule.eq_of_le_of_finrank_eq h (by rw [ℓ.2, ℓ'.2]))

lemma line_le_or_inf_eq_bot (P : Lines K N) (W : Submodule K (Fin N → K)) :
    P.1 ≤ W ∨ P.1 ⊓ W = ⊥ := by
  by_cases h : P.1 ≤ W
  · exact Or.inl h
  right
  have h1 : Module.finrank K (P.1 ⊓ W : Submodule K (Fin N → K)) ≤ 1 := by
    have := Submodule.finrank_mono (inf_le_left : P.1 ⊓ W ≤ P.1)
    rwa [P.2] at this
  have h2 : Module.finrank K (P.1 ⊓ W : Submodule K (Fin N → K)) ≠ 1 := by
    intro h'
    have := Submodule.eq_of_le_of_finrank_eq (inf_le_left : P.1 ⊓ W ≤ P.1) (h'.trans P.2.symm)
    exact h (this ▸ inf_le_right)
  exact Submodule.finrank_eq_zero.mp (by omega)

lemma finrank_sup_line (T : Submodule K (Fin N → K)) (P : Lines K N) (h : ¬ P.1 ≤ T) :
    Module.finrank K (T ⊔ P.1 : Submodule K (Fin N → K)) = Module.finrank K T + 1 := by
  have := Submodule.finrank_sup_add_finrank_inf_eq T P.1
  rw [inf_comm, (line_le_or_inf_eq_bot P T).resolve_left h, finrank_bot, P.2] at this
  omega

lemma finrank_sup_line_le (T : Submodule K (Fin N → K)) (P : Lines K N) :
    Module.finrank K (T ⊔ P.1 : Submodule K (Fin N → K)) ≤ Module.finrank K T + 1 := by
  by_cases h : P.1 ≤ T
  · rw [sup_eq_left.mpr h]; omega
  · rw [finrank_sup_line T P h]

lemma hyp_inf {H U S : Submodule K (Fin N → K)} (hH : IsHyp H U) (hSU : S ≤ U)
    (hS : ¬ S ≤ H) :
    Module.finrank K (S ⊓ H : Submodule K (Fin N → K)) + 1 = Module.finrank K S := by
  have hlt : H < H ⊔ S := lt_of_le_of_ne le_sup_left
    (fun h => hS ((le_sup_right : S ≤ H ⊔ S).trans h.symm.le))
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : Module.finrank K (H ⊔ S : Submodule K (Fin N → K)) ≤ Module.finrank K U :=
    Submodule.finrank_mono (sup_le hH.1 hSU)
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq H S
  rw [inf_comm] at h3
  have := hH.2
  omega

lemma join_finrank {P X : Lines K N} (h : P ≠ X) :
    Module.finrank K (P.1 ⊔ X.1 : Submodule K (Fin N → K)) = 2 := by
  have hX : ¬ X.1 ≤ P.1 := fun h' => h (line_eq_of_le h').symm
  rw [finrank_sup_line P.1 X hX, P.2]

lemma line_eq_join {L : Submodule K (Fin N → K)} (hL : Module.finrank K L = 2)
    {P Z : Lines K N} (hP : P.1 ≤ L) (hZ : Z.1 ≤ L) (h : P ≠ Z) : L = P.1 ⊔ Z.1 :=
  (Submodule.eq_of_le_of_finrank_eq (sup_le hP hZ) (by rw [join_finrank h, hL])).symm

lemma inf_finrank_one {T H L : Submodule K (Fin N → K)} (hH : IsHyp H T) (hLT : L ≤ T)
    (hL : Module.finrank K L = 2) (hLH : ¬ L ≤ H) :
    Module.finrank K (L ⊓ H : Submodule K (Fin N → K)) = 1 := by
  have := hyp_inf hH hLT hLH
  omega

lemma pt_unique {T H L : Submodule K (Fin N → K)} (hH : IsHyp H T) (hLT : L ≤ T)
    (hL : Module.finrank K L = 2) (hLH : ¬ L ≤ H) {X Y : Lines K N} (hX : X.1 ≤ L)
    (hXH : X.1 ≤ H) (hY : Y.1 ≤ L) (hYH : Y.1 ≤ H) : X = Y := by
  have h1 := inf_finrank_one hH hLT hL hLH
  have eX : X.1 = L ⊓ H := Submodule.eq_of_le_of_finrank_eq (le_inf hX hXH) (by rw [X.2, h1])
  have eY : Y.1 = L ⊓ H := Submodule.eq_of_le_of_finrank_eq (le_inf hY hYH) (by rw [Y.2, h1])
  exact Subtype.ext (eX.trans eY.symm)

lemma inter_pt {T H L : Submodule K (Fin N → K)} (hH : IsHyp H T) (hLT : L ≤ T)
    (hL : Module.finrank K L = 2) (hLH : ¬ L ≤ H) : ∃ X : Lines K N, X.1 ≤ L ∧ X.1 ≤ H :=
  ⟨⟨L ⊓ H, inf_finrank_one hH hLT hL hLH⟩, inf_le_left, inf_le_right⟩

lemma not_le_of_hyp_ne {T A B : Submodule K (Fin N → K)} (hA : IsHyp A T) (hB : IsHyp B T)
    (h : A ≠ B) : ¬ A ≤ B := fun h' =>
  h (Submodule.eq_of_le_of_finrank_eq h' (by have := hA.2; have := hB.2; omega))

/-- for `A ≤ T` of dimension `m+1` and a hyperplane `H` of `T`, at most `q^m` points of `A`
lie off `H` -/
lemma sdiff_le {T H A : Submodule K (Fin N → K)} (hH : IsHyp H T) (hAT : A ≤ T) {m : ℕ}
    (hA : Module.finrank K A = m + 1) : (pts A \ pts H).card ≤ Fintype.card K ^ m := by
  by_cases h : A ≤ H
  · rw [Finset.sdiff_eq_empty_iff_subset.mpr (pts_mono h)]
    simp
  · have hset : pts A \ pts H = pts A \ pts (A ⊓ H) := by
      ext ℓ
      simp only [Finset.mem_sdiff, mem_pts, le_inf_iff]
      tauto
    rw [hset, card_pts_sdiff inf_le_left]
    have := hyp_inf hH hAT h
    have e : Module.finrank K (A ⊓ H : Submodule K (Fin N → K)) = m := by omega
    rw [hA, e, th_succ_sub]

/-- a hyperplane whose holes lie in a hyperplane `Y` of it is heavy -/
lemma large_wt {p : ℕ} {c : Lines K N → ZMod p} {Hp Y : Submodule K (Fin N → K)} {m : ℕ}
    (hHp : Module.finrank K Hp = m + 2) (hY : IsHyp Y Hp)
    (hh : ∀ ℓ ∈ pts Hp, c ℓ = 0 → ℓ.1 ≤ Y) : Fintype.card K ^ (m + 1) ≤ wt Hp c := by
  have hc : (pts Hp \ pts Y).card = Fintype.card K ^ (m + 1) := by
    rw [card_pts_sdiff hY.1]
    have : Module.finrank K Y = m + 1 := by have := hY.2; omega
    rw [hHp, this, th_succ_sub]
  rw [← hc]
  apply le_wt Finset.sdiff_subset
  intro ℓ hℓ
  simp only [Finset.mem_sdiff, mem_pts] at hℓ
  intro h0
  exact hℓ.2 (hh ℓ ((mem_pts _ _).mpr hℓ.1) h0)

/-! ### Spanning -/
lemma exists_mid (B : Submodule K (Fin N → K)) (F : Finset (Lines K N)) :
    ∀ n, Module.finrank K B ≤ n →
      n ≤ Module.finrank K (B ⊔ F.sup (fun ℓ => ℓ.1) : Submodule K (Fin N → K)) →
      ∃ G ⊆ F, Module.finrank K (B ⊔ G.sup (fun ℓ => ℓ.1) : Submodule K (Fin N → K)) = n := by
  induction F using Finset.induction_on with
  | empty =>
    intro n h1 h2
    refine ⟨∅, subset_refl _, ?_⟩
    rw [Finset.sup_empty, sup_bot_eq] at h2 ⊢
    omega
  | insert a F _ ih =>
    intro n h1 h2
    have e : (B ⊔ (insert a F).sup (fun ℓ => ℓ.1) : Submodule K (Fin N → K)) =
        (B ⊔ F.sup (fun ℓ => ℓ.1)) ⊔ a.1 := by
      rw [Finset.sup_insert]
      exact (by rw [sup_comm a.1, ← sup_assoc] : B ⊔ (a.1 ⊔ F.sup (fun ℓ => ℓ.1)) = _)
    by_cases hn : n ≤ Module.finrank K (B ⊔ F.sup (fun ℓ => ℓ.1) : Submodule K (Fin N → K))
    · obtain ⟨G, hG, hG'⟩ := ih n h1 hn
      exact ⟨G, hG.trans (Finset.subset_insert _ _), hG'⟩
    · refine ⟨insert a F, subset_refl _, ?_⟩
      have := finrank_sup_line_le (B ⊔ F.sup (fun ℓ => ℓ.1)) a
      rw [e] at h2 ⊢
      omega

lemma sup_pts (T : Submodule K (Fin N → K)) : (pts T).sup (fun ℓ => ℓ.1) = T := by
  apply le_antisymm
  · exact Finset.sup_le (fun ℓ hℓ => (mem_pts _ _).mp hℓ)
  · intro v hv
    by_cases h0 : v = 0
    · rw [h0]; exact Submodule.zero_mem _
    let ℓ : Lines K N := ⟨K ∙ v, finrank_span_singleton h0⟩
    have hℓ : ℓ ∈ pts T := (mem_pts _ _).mpr ((Submodule.span_singleton_le_iff_mem _ _).mpr hv)
    exact Finset.le_sup (f := fun ℓ : Lines K N => ℓ.1) hℓ (Submodule.mem_span_singleton_self v)

lemma exists_hyp_above {W T : Submodule K (Fin N → K)} (hWT : W ≤ T)
    (h : Module.finrank K W < Module.finrank K T) : ∃ Hp, IsHyp Hp T ∧ W ≤ Hp := by
  have e : (W ⊔ (pts T).sup (fun ℓ => ℓ.1) : Submodule K (Fin N → K)) = T := by
    rw [sup_pts, sup_eq_right.mpr hWT]
  obtain ⟨G, hG, hGd⟩ := exists_mid W (pts T) (Module.finrank K T - 1) (by omega) (by rw [e]; omega)
  have hle : (W ⊔ G.sup (fun ℓ => ℓ.1) : Submodule K (Fin N → K)) ≤ T :=
    sup_le hWT (Finset.sup_le (fun ℓ hℓ => (mem_pts _ _).mp (hG hℓ)))
  exact ⟨_, ⟨hle, by omega⟩, le_sup_left⟩

lemma span_hyp {p : ℕ} (c : Lines K N → ZMod p) {T : Submodule K (Fin N → K)}
    (hT : 1 ≤ Module.finrank K T)
    (hno : ¬ ∃ Hp, IsHyp Hp T ∧ ∀ ℓ ∈ pts T, c ℓ = 0 → ℓ.1 ≤ Hp) :
    ∃ Hp0, IsHyp Hp0 T ∧ ¬ ∃ Y, IsHyp Y Hp0 ∧ ∀ ℓ ∈ pts Hp0, c ℓ = 0 → ℓ.1 ≤ Y := by
  set H := (pts T).filter (fun ℓ => c ℓ = 0)
  have hWT : H.sup (fun ℓ => ℓ.1) ≤ T :=
    Finset.sup_le (fun ℓ hℓ => (mem_pts _ _).mp (Finset.mem_filter.mp hℓ).1)
  have hfull : Module.finrank K T ≤ Module.finrank K (H.sup (fun ℓ => ℓ.1) : Submodule K (Fin N → K)) := by
    by_contra hlt
    obtain ⟨Hp, hHp, hle⟩ := exists_hyp_above hWT (by omega)
    exact hno ⟨Hp, hHp, fun ℓ hℓ h0 =>
      (Finset.le_sup (f := fun ℓ : Lines K N => ℓ.1) (Finset.mem_filter.mpr ⟨hℓ, h0⟩)).trans hle⟩
  obtain ⟨G, hG, hGd⟩ := exists_mid ⊥ H (Module.finrank K T - 1) (by simp)
    (by rw [bot_sup_eq]; omega)
  rw [bot_sup_eq] at hGd
  have hGT : G.sup (fun ℓ => ℓ.1) ≤ T := (Finset.sup_mono hG).trans hWT
  refine ⟨G.sup (fun ℓ => ℓ.1), ⟨hGT, by omega⟩, ?_⟩
  rintro ⟨Y, hY, hYh⟩
  have : G.sup (fun ℓ => ℓ.1) ≤ Y := by
    apply Finset.sup_le
    intro ℓ hℓ
    apply hYh ℓ ((mem_pts _ _).mpr (Finset.le_sup (f := fun ℓ : Lines K N => ℓ.1) hℓ))
    exact (Finset.mem_filter.mp (hG hℓ)).2
  have := Submodule.finrank_mono this
  have := hY.2
  omega

/-! ### Case 2: a small hyperplane missing a hole -/
lemma case2 (hq : 7 ≤ Fintype.card K) {p : ℕ} (c : Lines K N → ZMod p)
    {T : Submodule K (Fin N → K)}
    (hlines : ∀ L : Submodule K (Fin N → K), L ≤ T → Module.finrank K L = 2 →
      wt L c ≤ 2 ∨ Fintype.card K ≤ wt L c)
    {Hs0 : Submodule K (Fin N → K)} (hHs0 : IsHyp Hs0 T) {P : Lines K N} (hPT : P.1 ≤ T)
    (hcP : c P = 0) (hPHs : ¬ P.1 ≤ Hs0) :
    1 + ((pts Hs0).filter (fun ℓ => c ℓ = 0)).card * (Fintype.card K - 2) ≤
      ((pts T).filter (fun ℓ => c ℓ = 0)).card := by
  set q := Fintype.card K
  set H0 := (pts Hs0).filter (fun ℓ => c ℓ = 0)
  let E : Lines K N → Finset (Lines K N) := fun X =>
    ((pts (P.1 ⊔ X.1)).filter (fun ℓ => c ℓ = 0)).erase P
  have hX : ∀ X ∈ H0, X.1 ≤ Hs0 ∧ c X = 0 ∧ P ≠ X := by
    intro X hX
    have h := Finset.mem_filter.mp hX
    refine ⟨(mem_pts _ _).mp h.1, h.2, ?_⟩
    rintro rfl
    exact hPHs ((mem_pts _ _).mp h.1)
  have hLT : ∀ X ∈ H0, P.1 ⊔ X.1 ≤ T := fun X hX' =>
    sup_le hPT ((hX X hX').1.trans hHs0.1)
  have hLHs : ∀ X ∈ H0, ¬ P.1 ⊔ X.1 ≤ Hs0 := fun X _ h => hPHs (le_sup_left.trans h)
  have hEcard : ∀ X ∈ H0, q - 2 ≤ (E X).card := by
    intro X hX'
    obtain ⟨hXHs, hcX, hPX⟩ := hX X hX'
    have hd := join_finrank hPX
    have hsum := wt_add_holes (P.1 ⊔ X.1) c
    rw [hd, th_two] at hsum
    have h2 : 2 ≤ ((pts (P.1 ⊔ X.1)).filter (fun ℓ => c ℓ = 0)).card := by
      have : ({P, X} : Finset (Lines K N)) ⊆ (pts (P.1 ⊔ X.1)).filter (fun ℓ => c ℓ = 0) := by
        intro Z hZ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
        rcases hZ with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨(mem_pts _ _).mpr le_sup_left, hcP⟩
        · exact Finset.mem_filter.mpr ⟨(mem_pts _ _).mpr le_sup_right, hcX⟩
      have := Finset.card_le_card this
      rwa [Finset.card_pair hPX] at this
    have hw : wt (P.1 ⊔ X.1) c ≤ 2 := by
      rcases hlines _ (hLT X hX') hd with h | h
      · exact h
      · omega
    have hPm : P ∈ (pts (P.1 ⊔ X.1)).filter (fun ℓ => c ℓ = 0) :=
      Finset.mem_filter.mpr ⟨(mem_pts _ _).mpr le_sup_left, hcP⟩
    have := Finset.card_erase_of_mem hPm
    simp only [E]
    omega
  have hdisj : (H0 : Set (Lines K N)).PairwiseDisjoint E := by
    intro X hX' Y hY' hXY
    rw [Function.onFun, Finset.disjoint_left]
    intro Z hZX hZY
    simp only [E, Finset.mem_erase, Finset.mem_filter, mem_pts] at hZX hZY
    obtain ⟨hXHs, _, hPX⟩ := hX X hX'
    obtain ⟨hYHs, _, hPY⟩ := hX Y hY'
    have e1 := line_eq_join (join_finrank hPX) le_sup_left hZX.2.1 (Ne.symm hZX.1)
    have e2 := line_eq_join (join_finrank hPY) le_sup_left hZY.2.1 (Ne.symm hZY.1)
    have hXL : X.1 ≤ P.1 ⊔ Y.1 := by rw [e2, ← e1]; exact le_sup_right
    exact hXY (pt_unique hHs0 (hLT Y hY') (join_finrank hPY) (hLHs Y hY') hXL hXHs le_sup_right hYHs)
  have hsub : H0.biUnion E ⊆ ((pts T).filter (fun ℓ => c ℓ = 0)).erase P := by
    intro Z hZ
    obtain ⟨X, hX', hZX⟩ := Finset.mem_biUnion.mp hZ
    simp only [E, Finset.mem_erase, Finset.mem_filter, mem_pts] at hZX ⊢
    exact ⟨hZX.1, hZX.2.1.trans (hLT X hX'), hZX.2.2⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj] at h1
  have h2 := Finset.card_nsmul_le_sum H0 (fun X => (E X).card) (q - 2) hEcard
  have hPm : P ∈ (pts T).filter (fun ℓ => c ℓ = 0) :=
    Finset.mem_filter.mpr ⟨(mem_pts _ _).mpr hPT, hcP⟩
  have h3 := Finset.card_erase_of_mem hPm
  rw [smul_eq_mul] at h2
  have h4 : 1 ≤ ((pts T).filter (fun ℓ => c ℓ = 0)).card := Finset.card_pos.mpr ⟨P, hPm⟩
  omega

/-! ### Case 1: a support point off two heavy hyperplanes -/
lemma case1 (hq : 7 ≤ Fintype.card K) {p : ℕ} (c : Lines K N → ZMod p)
    {T : Submodule K (Fin N → K)}
    (hlines : ∀ L : Submodule K (Fin N → K), L ≤ T → Module.finrank K L = 2 →
      wt L c ≤ 2 ∨ Fintype.card K ≤ wt L c)
    {m : ℕ} (hT : Module.finrank K T = m + 3)
    {A B : Submodule K (Fin N → K)} (hA : IsHyp A T) (hB : IsHyp B T) (hAB : A ≠ B)
    {YA YB : Submodule K (Fin N → K)} (hYA : IsHyp YA A)
    (hhA : ∀ ℓ ∈ pts A, c ℓ = 0 → ℓ.1 ≤ YA) (hYB : IsHyp YB B)
    (hhB : ∀ ℓ ∈ pts B, c ℓ = 0 → ℓ.1 ≤ YB)
    {P : Lines K N} (hPT : P.1 ≤ T) (hcP : c P ≠ 0) (hPA : ¬ P.1 ≤ A) (hPB : ¬ P.1 ≤ B) :
    ∃ g, Fintype.card K ^ (m + 1) ≤ g + 2 * Fintype.card K ^ m ∧
      1 + wt A c + wt B c + g * (Fintype.card K - 3) ≤
        wt T c + th (Fintype.card K) (m + 1) := by
  set q := Fintype.card K
  have dA : Module.finrank K A = m + 2 := by have := hA.2; omega
  have dB : Module.finrank K B = m + 2 := by have := hB.2; omega
  have dYA : Module.finrank K YA = m + 1 := by have := hYA.2; omega
  have dYB : Module.finrank K YB = m + 1 := by have := hYB.2; omega
  have hAB' := not_le_of_hyp_ne hA hB hAB
  have dAB : Module.finrank K (A ⊓ B : Submodule K (Fin N → K)) = m + 1 := by
    have := hyp_inf hB hA.1 hAB'; omega
  -- the subspace `Z2 = (YB + P) ∩ A`
  have hPYB : ¬ P.1 ≤ YB := fun h => hPB (h.trans hYB.1)
  have hYBP_T : YB ⊔ P.1 ≤ T := sup_le (hYB.1.trans hB.1) hPT
  have hYBP_A : ¬ YB ⊔ P.1 ≤ A := fun h => hPA (le_sup_right.trans h)
  have dZ2 : Module.finrank K ((YB ⊔ P.1) ⊓ A : Submodule K (Fin N → K)) = m + 1 := by
    have := hyp_inf hA hYBP_T hYBP_A
    rw [finrank_sup_line YB P hPYB, dYB] at this
    omega
  set Z2 := ((YB ⊔ P.1) ⊓ A : Submodule K (Fin N → K))
  have hZ2T : Z2 ≤ T := inf_le_right.trans hA.1
  -- the good points of `A`
  set G := ((pts A \ pts B) \ (pts YA \ pts B)) \ (pts Z2 \ pts B)
  have hA0 : (pts A \ pts B).card = q ^ (m + 1) := by
    have hset : pts A \ pts B = pts A \ pts (A ⊓ B) := by
      ext ℓ
      simp only [Finset.mem_sdiff, mem_pts, le_inf_iff]
      tauto
    rw [hset, card_pts_sdiff inf_le_left, dA, dAB, th_succ_sub]
  have hYAc : (pts YA \ pts B).card ≤ q ^ m := sdiff_le hB (hYA.1.trans hA.1) dYA
  have hZ2c : (pts Z2 \ pts B).card ≤ q ^ m := sdiff_le hB hZ2T dZ2
  have hG : q ^ (m + 1) ≤ G.card + 2 * q ^ m := by
    have h1 : (pts A \ pts B).card - (pts YA \ pts B).card ≤
        ((pts A \ pts B) \ (pts YA \ pts B)).card := Finset.le_card_sdiff _ _
    have h2 : ((pts A \ pts B) \ (pts YA \ pts B)).card - (pts Z2 \ pts B).card ≤ G.card :=
      Finset.le_card_sdiff _ _
    omega
  have memG : ∀ X ∈ G, X.1 ≤ A ∧ ¬ X.1 ≤ B ∧ ¬ X.1 ≤ YA ∧ ¬ X.1 ≤ Z2 := by
    intro X hX
    simp only [G, Finset.mem_sdiff, mem_pts] at hX
    tauto
  -- the extra support points on the line `P + X`
  let E : Lines K N → Finset (Lines K N) := fun X =>
    (pts (P.1 ⊔ X.1)).filter (fun Z => c Z ≠ 0 ∧ ¬ Z.1 ≤ A ∧ ¬ Z.1 ≤ B ∧ Z ≠ P)
  have hPX : ∀ X ∈ G, P ≠ X := by
    rintro X hX rfl
    exact hPA (memG P hX).1
  have hLT : ∀ X ∈ G, P.1 ⊔ X.1 ≤ T := fun X hX => sup_le hPT ((memG X hX).1.trans hA.1)
  have hLA : ∀ X ∈ G, ¬ P.1 ⊔ X.1 ≤ A := fun X _ h => hPA (le_sup_left.trans h)
  have hLB : ∀ X ∈ G, ¬ P.1 ⊔ X.1 ≤ B := fun X _ h => hPB (le_sup_left.trans h)
  have hEcard : ∀ X ∈ G, q - 3 ≤ (E X).card := by
    intro X hX
    obtain ⟨hXA, hXB, hXYA, hXZ2⟩ := memG X hX
    have hd := join_finrank (hPX X hX)
    obtain ⟨X2, hX2L, hX2B⟩ := inter_pt hB (hLT X hX) hd (hLB X hX)
    have hcX : c X ≠ 0 := fun h0 => hXYA (hhA X ((mem_pts _ _).mpr hXA) h0)
    have hPX2 : P ≠ X2 := by rintro rfl; exact hPB hX2B
    have hXX2 : X ≠ X2 := by rintro rfl; exact hXB hX2B
    have hcX2 : c X2 ≠ 0 := by
      intro h0
      have hX2YB := hhB X2 ((mem_pts _ _).mpr hX2B) h0
      have e := line_eq_join hd le_sup_left hX2L hPX2
      have hle : P.1 ⊔ X.1 ≤ YB ⊔ P.1 := by
        rw [e]; exact sup_le le_sup_right (hX2YB.trans le_sup_left)
      exact hXZ2 (le_inf ((le_sup_right : X.1 ≤ P.1 ⊔ X.1).trans hle) hXA)
    have h3 : 3 ≤ wt (P.1 ⊔ X.1) c := by
      have hc3 : ({P, X, X2} : Finset (Lines K N)).card = 3 :=
        Finset.card_eq_three.mpr ⟨P, X, X2, hPX X hX, hPX2, hXX2, rfl⟩
      rw [← hc3]
      apply le_wt
      · intro Z hZ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
        rw [mem_pts]
        rcases hZ with rfl | rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
        · exact hX2L
      · intro Z hZ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hZ
        rcases hZ with rfl | rfl | rfl <;> assumption
    have hq' : q ≤ wt (P.1 ⊔ X.1) c := by
      rcases hlines _ (hLT X hX) hd with h | h
      · omega
      · exact h
    have hsub : (pts (P.1 ⊔ X.1)).filter (fun Z => c Z ≠ 0) ⊆ E X ∪ {P, X, X2} := by
      intro Z hZ
      have hZ' := Finset.mem_filter.mp hZ
      have hZL := (mem_pts _ _).mp hZ'.1
      by_cases hZA : Z.1 ≤ A
      · have := pt_unique hA (hLT X hX) hd (hLA X hX) hZL hZA le_sup_right hXA
        simp [this]
      by_cases hZB : Z.1 ≤ B
      · have := pt_unique hB (hLT X hX) hd (hLB X hX) hZL hZB hX2L hX2B
        simp [this]
      by_cases hZP : Z = P
      · simp [hZP]
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hZ'.1, hZ'.2, hZA, hZB, hZP⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (E X) {P, X, X2}
    have h4 : ({P, X, X2} : Finset (Lines K N)).card ≤ 3 := Finset.card_le_three
    have : wt (P.1 ⊔ X.1) c = ((pts (P.1 ⊔ X.1)).filter (fun Z => c Z ≠ 0)).card := rfl
    omega
  have hdisj : (G : Set (Lines K N)).PairwiseDisjoint E := by
    intro X hX Y hY hXY
    rw [Function.onFun, Finset.disjoint_left]
    intro Z hZX hZY
    simp only [E, Finset.mem_filter, mem_pts] at hZX hZY
    have e1 := line_eq_join (join_finrank (hPX X hX)) le_sup_left hZX.1 (Ne.symm hZX.2.2.2.2)
    have e2 := line_eq_join (join_finrank (hPX Y hY)) le_sup_left hZY.1 (Ne.symm hZY.2.2.2.2)
    have hXL : X.1 ≤ P.1 ⊔ Y.1 := by rw [e2, ← e1]; exact le_sup_right
    exact hXY (pt_unique hA (hLT Y hY) (join_finrank (hPX Y hY)) (hLA Y hY) hXL (memG X hX).1
      le_sup_right (memG Y hY).1)
  -- assemble
  set SA := (pts A).filter (fun Z => c Z ≠ 0)
  set SB := (pts B).filter (fun Z => c Z ≠ 0)
  have hD1 : Disjoint (SA ∪ SB) (G.biUnion E) := by
    rw [Finset.disjoint_left]
    intro Z hZ hZE
    obtain ⟨X, _, hZX⟩ := Finset.mem_biUnion.mp hZE
    simp only [E, Finset.mem_filter, mem_pts] at hZX
    simp only [SA, SB, Finset.mem_union, Finset.mem_filter, mem_pts] at hZ
    rcases hZ with h | h
    · exact hZX.2.2.1 h.1
    · exact hZX.2.2.2.1 h.1
  have hPnot : P ∉ (SA ∪ SB) ∪ G.biUnion E := by
    intro h
    simp only [Finset.mem_union, SA, SB, Finset.mem_filter, mem_pts] at h
    rcases h with (h | h) | h
    · exact hPA h.1
    · exact hPB h.1
    · obtain ⟨X, _, hZX⟩ := Finset.mem_biUnion.mp h
      simp only [E, Finset.mem_filter] at hZX
      exact hZX.2.2.2.2 rfl
  have hall : insert P ((SA ∪ SB) ∪ G.biUnion E) ⊆ pts T := by
    intro Z hZ
    rw [mem_pts]
    simp only [Finset.mem_insert, Finset.mem_union, SA, SB, Finset.mem_filter, mem_pts] at hZ
    rcases hZ with rfl | (h | h) | h
    · exact hPT
    · exact h.1.trans hA.1
    · exact h.1.trans hB.1
    · obtain ⟨X, hX, hZX⟩ := Finset.mem_biUnion.mp h
      simp only [E, Finset.mem_filter, mem_pts] at hZX
      exact hZX.1.trans (hLT X hX)
  have hallc : ∀ Z ∈ insert P ((SA ∪ SB) ∪ G.biUnion E), c Z ≠ 0 := by
    intro Z hZ
    simp only [Finset.mem_insert, Finset.mem_union, SA, SB, Finset.mem_filter] at hZ
    rcases hZ with rfl | (h | h) | h
    · exact hcP
    · exact h.2
    · exact h.2
    · obtain ⟨X, _, hZX⟩ := Finset.mem_biUnion.mp h
      simp only [E, Finset.mem_filter] at hZX
      exact hZX.2.1
  have hW := le_wt hall hallc
  rw [Finset.card_insert_of_notMem hPnot, Finset.card_union_of_disjoint hD1,
    Finset.card_biUnion hdisj] at hW
  have hsum := Finset.card_nsmul_le_sum G (fun X => (E X).card) (q - 3) hEcard
  rw [smul_eq_mul] at hsum
  have hUI := Finset.card_union_add_card_inter SA SB
  have hI : (SA ∩ SB).card ≤ th q (m + 1) := by
    rw [← dAB, ← pts_card]
    apply Finset.card_le_card
    intro Z hZ
    simp only [SA, SB, Finset.mem_inter, Finset.mem_filter, mem_pts] at hZ
    rw [mem_pts]
    exact le_inf hZ.1.1 hZ.2.1
  have eA : wt A c = SA.card := rfl
  have eB : wt B c = SB.card := rfl
  refine ⟨G.card, hG, ?_⟩
  omega

/-! ### Numerical endgames -/
lemma num1 (q x t g w1 w2 wT hT h0 : ℕ) (hq : 7 ≤ q) (ht : t < x) (hg : x * q ≤ g + 2 * x)
    (h1 : 1 + w1 + w2 + g * (q - 3) ≤ wT + (t + x)) (hw1 : x * q ≤ w1) (hw2 : x * q ≤ w2)
    (hh0 : t + x * (1 + q) ≤ h0 + (2 * x + t)) (h2 : 1 + h0 * (q - 2) ≤ hT)
    (hsum : wT + hT = t + x * (1 + q + q * q)) : False := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 7 := ⟨q - 7, by omega⟩
  have e3 : r + 7 - 3 = r + 4 := by omega
  have e2 : r + 7 - 2 = r + 5 := by omega
  rw [e3] at h1
  rw [e2] at h2
  have hg' : x * (r + 5) ≤ g := by nlinarith
  have hh0' : x * (r + 6) ≤ h0 := by nlinarith
  nlinarith [Nat.mul_le_mul_right (r + 4) hg', Nat.mul_le_mul_right (r + 5) hh0']

lemma num2 (q x t n n' wT : ℕ) (hq : 7 ≤ q) (hx : 1 ≤ x) (hqt : q * t + 1 = t + x)
    (hn : n ≤ 2) (hsum : n + n' = t + x * (1 + q + q * q))
    (h : wT * (t + x * (1 + q)) ≤ n * (t + x * (1 + q)) + n' * (2 * x + t)) :
    wT ≤ 2 * (x * q) + (t + x) := by
  by_contra hc
  push Not at hc
  have hB : 2 * x + t ≤ t + x * (1 + q) := by nlinarith
  have k1 : (2 * (x * q) + (t + x) + 1) * (t + x * (1 + q)) ≤ wT * (t + x * (1 + q)) :=
    Nat.mul_le_mul_right _ hc
  have k2 : n * (t + x * (1 + q) - (2 * x + t)) ≤ 2 * (t + x * (1 + q) - (2 * x + t)) :=
    Nat.mul_le_mul_right _ hn
  have k3 : (n + n') * (2 * x + t) = (t + x * (1 + q + q * q)) * (2 * x + t) := by rw [hsum]
  obtain ⟨d, hd⟩ : ∃ d, t + x * (1 + q) = (2 * x + t) + d := ⟨_, (Nat.add_sub_of_le hB).symm⟩
  rw [hd, Nat.add_sub_cancel_left] at k2
  rw [hd] at k1 h
  nlinarith

/-! ### The induction step -/
lemma step (hq : 7 ≤ Fintype.card K) {p : ℕ} (c : Lines K N → ZMod p)
    {T : Submodule K (Fin N → K)}
    (hlines : ∀ L : Submodule K (Fin N → K), L ≤ T → Module.finrank K L = 2 →
      wt L c ≤ 2 ∨ Fintype.card K ≤ wt L c)
    {m : ℕ} (hT : Module.finrank K T = m + 3)
    (IH : ∀ Hp, IsHyp Hp T → wt Hp c ≤ 2 * Fintype.card K ^ m + th (Fintype.card K) m ∨
      ∃ Y, IsHyp Y Hp ∧ ∀ ℓ ∈ pts Hp, c ℓ = 0 → ℓ.1 ≤ Y) :
    wt T c ≤ 2 * Fintype.card K ^ (m + 1) + th (Fintype.card K) (m + 1) ∨
      ∃ Hp, IsHyp Hp T ∧ ∀ ℓ ∈ pts T, c ℓ = 0 → ℓ.1 ≤ Hp := by
  by_cases hH : ∃ Hp, IsHyp Hp T ∧ ∀ ℓ ∈ pts T, c ℓ = 0 → ℓ.1 ≤ Hp
  · exact Or.inr hH
  left
  set q := Fintype.card K
  set x := q ^ m
  set t := th q m
  have ht : t < x := th_lt_pow q (by omega) m
  have hqt : q * t + 1 = t + x := th_succ' q m
  have e1 : th q (m + 1) = t + x := by rw [th_add, th_one, mul_one]
  have e2 : th q (m + 2) = t + x * (1 + q) := by rw [th_add, th_two]
  have e3 : th q (m + 3) = t + x * (1 + q + q * q) := by rw [th_add, th_three]
  have epow : q ^ (m + 1) = x * q := pow_succ q m
  rw [epow, e1]
  have dH : ∀ Hp, IsHyp Hp T → Module.finrank K Hp = m + 2 := fun Hp h => by
    have := h.2; omega
  -- a small hyperplane missing a hole
  obtain ⟨Hp0, hHp0, hno0⟩ := span_hyp c (by omega) hH
  have hsmall0 : wt Hp0 c ≤ 2 * x + t := by
    have := (IH Hp0 hHp0).resolve_right hno0
    omega
  obtain ⟨P0, hP0T, hcP0, hP0⟩ : ∃ P0 ∈ pts T, c P0 = 0 ∧ ¬ P0.1 ≤ Hp0 := by
    by_contra hcon
    push Not at hcon
    exact hH ⟨Hp0, hHp0, hcon⟩
  have hc2 := case2 hq c hlines hHp0 ((mem_pts _ _).mp hP0T) hcP0 hP0
  have hh0 := wt_add_holes Hp0 c
  rw [dH Hp0 hHp0, e2] at hh0
  have hhT := wt_add_holes T c
  rw [hT, e3] at hhT
  -- the non-small hyperplanes
  set NS := (hyps ⊥ T).filter (fun Hp => 2 * x + t < wt Hp c)
  by_cases hn : NS.card ≤ 2
  · have hs := hyps_sum (T := ⊥) (U := T) bot_le (by rw [finrank_bot, hT]; omega) c
    rw [wt_bot, finrank_bot, hT] at hs
    have e4 : m + 3 - 0 - 1 = m + 2 := by omega
    rw [e4, e2, mul_zero, zero_add, Nat.sub_zero] at hs
    have hsplit := Finset.sum_filter_add_sum_filter_not (hyps ⊥ T)
      (fun Hp => 2 * x + t < wt Hp c) (fun V => wt V c)
    have b1 := Finset.sum_le_card_nsmul NS (fun V => wt V c) (t + x * (1 + q)) (by
      intro V hV
      have hV' := (mem_hyps.mp (Finset.mem_filter.mp hV).1).1
      have := wt_le V c
      rw [dH V hV', e2] at this
      exact this)
    have b2 := Finset.sum_le_card_nsmul ((hyps ⊥ T).filter (fun Hp => ¬ 2 * x + t < wt Hp c))
      (fun V => wt V c) (2 * x + t) (by
        intro V hV
        have := (Finset.mem_filter.mp hV).2
        omega)
    have hcards := Finset.card_filter_add_card_filter_not (s := hyps ⊥ T)
      (fun Hp => 2 * x + t < wt Hp c)
    rw [hyps_card bot_le, finrank_bot, hT, Nat.sub_zero, e3] at hcards
    rw [smul_eq_mul] at b1 b2
    apply num2 q x t NS.card _ (wt T c) hq (Nat.one_le_iff_ne_zero.mpr (by positivity)) hqt hn
      hcards
    rw [mul_comm (wt T c)]
    simp only [NS] at b1 ⊢
    omega
  · obtain ⟨A, hA, B, hB, C, hC, hAB, hAC, hBC⟩ := Finset.two_lt_card.mp (show 2 < NS.card by omega)
    have info : ∀ V ∈ NS, IsHyp V T ∧ ∃ Y, IsHyp Y V ∧ ∀ ℓ ∈ pts V, c ℓ = 0 → ℓ.1 ≤ Y := by
      intro V hV
      have h := Finset.mem_filter.mp hV
      have hV' := (mem_hyps.mp h.1).1
      refine ⟨hV', (IH V hV').resolve_left ?_⟩
      omega
    obtain ⟨hA', YA, hYA, hhA⟩ := info A hA
    obtain ⟨hB', YB, hYB, hhB⟩ := info B hB
    obtain ⟨hC', YC, hYC, hhC⟩ := info C hC
    have wA : x * q ≤ wt A c := by rw [← epow]; exact large_wt (dH A hA') hYA hhA
    have wB : x * q ≤ wt B c := by rw [← epow]; exact large_wt (dH B hB') hYB hhB
    have wC : x * q ≤ wt C c := by rw [← epow]; exact large_wt (dH C hC') hYC hhC
    by_cases hP : ∃ P ∈ pts T, c P ≠ 0 ∧ ¬ P.1 ≤ A ∧ ¬ P.1 ≤ B
    · obtain ⟨P, hPT, hcP, hPA, hPB⟩ := hP
      obtain ⟨g, hg, h1⟩ := case1 hq c hlines hT hA' hB' hAB hYA hhA hYB hhB
        ((mem_pts _ _).mp hPT) hcP hPA hPB
      have hg' : q ^ (m + 1) ≤ g + 2 * x := hg
      rw [epow] at hg'
      have h1' : 1 + wt A c + wt B c + g * (q - 3) ≤ wt T c + th q (m + 1) := h1
      rw [e1] at h1'
      exact (num1 q x t g (wt A c) (wt B c) (wt T c) ((pts T).filter (fun ℓ => c ℓ = 0)).card
        ((pts Hp0).filter (fun ℓ => c ℓ = 0)).card hq ht hg' h1' wA wB (by omega) hc2
        (by omega)).elim
    · push Not at hP
      exfalso
      have dCA : Module.finrank K (C ⊓ A : Submodule K (Fin N → K)) = m + 1 := by
        have := hyp_inf hA' hC'.1 (not_le_of_hyp_ne hC' hA' (Ne.symm hAC)); rw [dH C hC'] at this
        omega
      have dCB : Module.finrank K (C ⊓ B : Submodule K (Fin N → K)) = m + 1 := by
        have := hyp_inf hB' hC'.1 (not_le_of_hyp_ne hC' hB' (Ne.symm hBC)); rw [dH C hC'] at this
        omega
      have hsub : (pts C).filter (fun Z => c Z ≠ 0) ⊆ pts (C ⊓ A) ∪ pts (C ⊓ B) := by
        intro Z hZ
        have hZ' := Finset.mem_filter.mp hZ
        have hZC := (mem_pts _ _).mp hZ'.1
        rw [Finset.mem_union, mem_pts, mem_pts]
        by_cases hZA : Z.1 ≤ A
        · exact Or.inl (le_inf hZC hZA)
        · exact Or.inr (le_inf hZC (hP Z ((mem_pts _ _).mpr (hZC.trans hC'.1)) hZ'.2 hZA))
      have k1 := Finset.card_le_card hsub
      have k2 := Finset.card_union_le (pts (C ⊓ A)) (pts (C ⊓ B))
      rw [pts_card, pts_card, dCA, dCB, e1] at k2
      have : wt C c = ((pts C).filter (fun Z => c Z ≠ 0)).card := rfl
      nlinarith

/-! ### The classification -/
lemma base {p : ℕ} (c : Lines K N → ZMod p)
    {T : Submodule K (Fin N → K)} (hT : Module.finrank K T = 2)
    (hlines : ∀ L : Submodule K (Fin N → K), L ≤ T → Module.finrank K L = 2 →
      wt L c ≤ 2 ∨ Fintype.card K ≤ wt L c) :
    wt T c ≤ 2 ∨ ∃ Hp, IsHyp Hp T ∧ ∀ ℓ ∈ pts T, c ℓ = 0 → ℓ.1 ≤ Hp := by
  rcases hlines T le_rfl hT with h | h
  · exact Or.inl h
  right
  have hs := wt_add_holes T c
  rw [hT, th_two] at hs
  have h1 : ((pts T).filter (fun ℓ => c ℓ = 0)).card ≤ 1 := by omega
  by_cases hex : ∃ Z ∈ pts T, c Z = 0
  · obtain ⟨Z, hZT, hcZ⟩ := hex
    refine ⟨Z.1, ⟨(mem_pts _ _).mp hZT, by rw [Z.2, hT]⟩, ?_⟩
    intro ℓ hℓ hcℓ
    have := Finset.card_le_one.mp h1 ℓ (Finset.mem_filter.mpr ⟨hℓ, hcℓ⟩) Z
      (Finset.mem_filter.mpr ⟨hZT, hcZ⟩)
    rw [this]
  · obtain ⟨Hp, hHp, _⟩ := exists_hyp_above (bot_le : (⊥ : Submodule K (Fin N → K)) ≤ T)
      (by rw [finrank_bot, hT]; omega)
    exact ⟨Hp, hHp, fun ℓ hℓ hcℓ => absurd ⟨ℓ, hℓ, hcℓ⟩ hex⟩

theorem K_class (hq : 7 ≤ Fintype.card K) {p : ℕ} (c : Lines K N → ZMod p)
    {T : Submodule K (Fin N → K)} (hT : 2 ≤ Module.finrank K T)
    (hlines : ∀ L : Submodule K (Fin N → K), L ≤ T → Module.finrank K L = 2 →
      wt L c ≤ 2 ∨ Fintype.card K ≤ wt L c) :
    wt T c ≤ 2 * Fintype.card K ^ (Module.finrank K T - 2) +
        th (Fintype.card K) (Module.finrank K T - 2) ∨
      ∃ Hp, IsHyp Hp T ∧ ∀ ℓ ∈ pts T, c ℓ = 0 → ℓ.1 ≤ Hp := by
  suffices H : ∀ k, 2 ≤ k → ∀ T : Submodule K (Fin N → K), Module.finrank K T = k →
      (∀ L : Submodule K (Fin N → K), L ≤ T → Module.finrank K L = 2 →
        wt L c ≤ 2 ∨ Fintype.card K ≤ wt L c) →
      wt T c ≤ 2 * Fintype.card K ^ (k - 2) + th (Fintype.card K) (k - 2) ∨
        ∃ Hp, IsHyp Hp T ∧ ∀ ℓ ∈ pts T, c ℓ = 0 → ℓ.1 ≤ Hp from
    H _ hT T rfl hlines
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro T hT2 hl
    have := base c hT2 hl
    simpa [th] using this
  | succ k hk ih =>
    intro T hTk hl
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    have e : m + 2 + 1 - 2 = m + 1 := by omega
    rw [e]
    apply step hq c hl (m := m) (by rw [hTk])
    intro Hp hHp
    have dHp : Module.finrank K Hp = m + 2 := by have := hHp.2; omega
    have := ih Hp dHp (fun L hL hL2 => hl L (hL.trans hHp.1) hL2)
    rwa [Nat.add_sub_cancel] at this

end ProxGapTight.Dev.Q366.PartK
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ## Part K: ADSW Lemma 3.2.4 (pure combinatorics) -/
alias K_class := ProxGapTight.Dev.Q366.PartK.K_class

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace ProxGapTight.Dev.Q366.PartT
open ProxGapTight ProxGapTight.Dev.Q366
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-!
Part T of q366: ADSW Theorem 3.2.6 by induction on the weight.

* Case II (some hyperplane `P1` of `U` has its holes inside a hyperplane of `P1`): a nonzero value
  `α` is taken on more points of `P1` than there are holes (pigeonhole), so `c - α 1_{P1}` is
  lighter, hence a two-combination, and `THREE` finishes.
* Case I (otherwise `K_class` makes every hyperplane light, so the restriction to every hyperplane
  is a two-combination): `c = 0`, by the plane argument of PLAN §6.
-/
/-! ## Basic API -/
theorem mem_pts {U : Submodule K (Fin N → K)} {ℓ : Lines K N} : ℓ ∈ pts U ↔ ℓ.1 ≤ U := by
  unfold pts; simp

/-- the support of `c` in `U` -/
noncomputable def supp {p : ℕ} (U : Submodule K (Fin N → K)) (c : Lines K N → ZMod p) :
    Finset (Lines K N) := by
  classical exact (pts U).filter (fun ℓ => c ℓ ≠ 0)

theorem wt_eq {p : ℕ} (U : Submodule K (Fin N → K)) (c : Lines K N → ZMod p) :
    wt U c = (supp U c).card := rfl

theorem mem_supp {p : ℕ} {U : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
    {ℓ : Lines K N} : ℓ ∈ supp U c ↔ ℓ.1 ≤ U ∧ c ℓ ≠ 0 := by
  unfold supp; simp [mem_pts]

theorem ind_le {p : ℕ} {W : Submodule K (Fin N → K)} {ℓ : Lines K N} (h : ℓ.1 ≤ W) :
    ind p W ℓ = 1 := by
  classical
  unfold ind; rw [Set.indicator_apply]; simp [h]

theorem ind_nle {p : ℕ} {W : Submodule K (Fin N → K)} {ℓ : Lines K N} (h : ¬ ℓ.1 ≤ W) :
    ind p W ℓ = 0 := by
  classical
  unfold ind; rw [Set.indicator_apply]; simp [h]

theorem res_le {p : ℕ} {T : Submodule K (Fin N → K)} {c : Lines K N → ZMod p} {ℓ : Lines K N}
    (h : ℓ.1 ≤ T) : res T c ℓ = c ℓ := by
  unfold res; simp [h]

open Classical in
theorem pts_inter (A B : Submodule K (Fin N → K)) : pts A ∩ pts B = pts (A ⊓ B) := by
  ext ℓ; simp [mem_pts]

theorem pts_card' {U : Submodule K (Fin N → K)} {k : ℕ} (h : Module.finrank K U = k) :
    (pts U).card = th (Fintype.card K) k := by
  rw [pts_card, h]

theorem mem_hyps {T U V : Submodule K (Fin N → K)} : V ∈ hyps T U ↔ IsHyp V U ∧ T ≤ V := by
  unfold hyps; simp

theorem mem_ext {T U V : Submodule K (Fin N → K)} :
    V ∈ ext T U ↔ T ≤ V ∧ V ≤ U ∧ Module.finrank K V = Module.finrank K T + 1 := by
  unfold ext; simp

theorem val2 {p : ℕ} {S A B : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
    {α β : ZMod p} (hrep : res S c = α • ind p A + β • ind p B) {Y : Lines K N}
    (hY : Y.1 ≤ S) : c Y = α * ind p A Y + β * ind p B Y := by
  have := congrFun hrep Y
  rw [res_le hY] at this
  simpa using this

/-! ## Arithmetic of `th` -/
theorem th_succ (q k : ℕ) : th q (k + 1) = th q k + q ^ k := Finset.sum_range_succ _ _

theorem th_one (q : ℕ) : th q 1 = 1 := by simp [th]

theorem th_rec (q k : ℕ) : th q (k + 1) = q * th q k + 1 := by
  unfold th
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

theorem th_mono (q : ℕ) {k k' : ℕ} (h : k ≤ k') : th q k ≤ th q k' :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

/-- `(q - 1) θ(k) + 1 = q^k`, stated with `q = r + 1` -/
theorem th_mul (r k : ℕ) : r * th (r + 1) k + 1 = (r + 1) ^ k := by
  induction k with
  | zero => simp [th]
  | succ k ih => rw [th_succ, pow_succ]; nlinarith [ih]

/-- `2θ(k) < q^k` for `q ≥ 3`, `k ≥ 1` -/
theorem two_th_lt (q k : ℕ) (hq : 3 ≤ q) (hk : 1 ≤ k) : 2 * th q k < q ^ k := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h := th_mul r k
  have : 1 ≤ th (r + 1) k := by
    have := th_mono (r + 1) hk; rw [th_one] at this; exact this
  nlinarith

/-! ## Linear algebra -/
theorem fr_mono {T U : Submodule K (Fin N → K)} (h : T ≤ U) :
    Module.finrank K T ≤ Module.finrank K U := Submodule.finrank_mono h

theorem eq_of_fr {T U : Submodule K (Fin N → K)} (h : T ≤ U)
    (h' : Module.finrank K U ≤ Module.finrank K T) : T = U :=
  Submodule.eq_of_le_of_finrank_le h h'

theorem line_eq_of_le {Y X : Lines K N} (h : Y.1 ≤ X.1) : Y = X :=
  Subtype.ext (eq_of_fr h (by rw [Y.2, X.2]))

/-- two distinct hyperplanes of `S` meet in a hyperplane of each -/
theorem hyp_inf {S A L : Submodule K (Fin N → K)} (hA : IsHyp A S) (hL : IsHyp L S)
    (hne : A ≠ L) : Module.finrank K ↥(L ⊓ A) + 1 = Module.finrank K L := by
  have hA2 := hA.2
  have hL2 := hL.2
  have h1 : L ⊔ A ≤ S := sup_le hL.1 hA.1
  have h1' := fr_mono h1
  have h2 : Module.finrank K ↥(L ⊔ A) = Module.finrank K S := by
    by_contra h
    have h3 : Module.finrank K ↥(L ⊔ A) ≤ Module.finrank K L := by omega
    have hLA : L = L ⊔ A := eq_of_fr le_sup_left h3
    have hAL : A ≤ L := hLA ▸ le_sup_right
    exact hne (eq_of_fr hAL (by omega))
  have := Submodule.finrank_sup_add_finrank_inf_eq L A
  omega

theorem fr_sup_line (U : Submodule K (Fin N → K)) (ℓ : Lines K N) (h : ¬ ℓ.1 ≤ U) :
    Module.finrank K ↥(U ⊔ ℓ.1) = Module.finrank K U + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq U ℓ.1
  have h0 : Module.finrank K ↥(U ⊓ ℓ.1) = 0 := by
    have h2 : Module.finrank K ↥(U ⊓ ℓ.1) ≤ 1 := by
      have := fr_mono (inf_le_right : U ⊓ ℓ.1 ≤ ℓ.1); rw [ℓ.2] at this; exact this
    by_contra h0
    have e := eq_of_fr (inf_le_right : U ⊓ ℓ.1 ≤ ℓ.1) (by rw [ℓ.2]; omega)
    exact h (e ▸ inf_le_left)
  rw [h0, ℓ.2] at h1
  omega

/-- a point of `U` outside `T` when `T` is smaller -/
theorem exists_point {T U : Submodule K (Fin N → K)} (h : T ≤ U)
    (hlt : Module.finrank K T < Module.finrank K U) : ∃ Y : Lines K N, Y.1 ≤ U ∧ ¬ Y.1 ≤ T := by
  have hTU : T < U := lt_of_le_of_ne h (by rintro rfl; omega)
  obtain ⟨v, hvU, hvT⟩ := SetLike.exists_of_lt hTU
  have hv0 : v ≠ 0 := fun h0 => hvT (h0 ▸ T.zero_mem)
  refine ⟨⟨K ∙ v, finrank_span_singleton hv0⟩, ?_, ?_⟩
  · exact (Submodule.span_singleton_le_iff_mem v U).mpr hvU
  · intro hle
    exact hvT ((Submodule.span_singleton_le_iff_mem v T).mp hle)

theorem exists_plane_aux {L U : Submodule K (Fin N → K)} {X Y1 Y2 : Lines K N} (hXL : X.1 ≤ L)
    (hLU : L ≤ U) (hdim : Module.finrank K L + 2 = Module.finrank K U) (hY1U : Y1.1 ≤ U)
    (hY2U : Y2.1 ≤ U)
    (h3 : Module.finrank K U ≤ Module.finrank K ↥(X.1 ⊔ Y1.1 ⊔ Y2.1 ⊔ L))
    (h5 : Module.finrank K ↥(X.1 ⊔ Y1.1 ⊔ Y2.1) ≤ 3) :
    ∃ pl : Submodule K (Fin N → K), pl ≤ U ∧ Module.finrank K pl = 3 ∧ X.1 ≤ pl ∧
      pl ⊓ L = X.1 := by
  generalize hpl : X.1 ⊔ Y1.1 ⊔ Y2.1 = pl at h3 h5
  have hplU : pl ≤ U := hpl ▸ sup_le (sup_le (hXL.trans hLU) hY1U) hY2U
  have hXpl : X.1 ≤ pl := hpl ▸ le_sup_left.trans le_sup_left
  have h4 := fr_mono (sup_le hplU hLU : pl ⊔ L ≤ U)
  have h6 := Submodule.finrank_sup_add_finrank_inf_eq pl L
  have h7 : X.1 ≤ pl ⊓ L := le_inf hXpl hXL
  have h8 := fr_mono h7
  have hX1 := X.2
  have h9 : pl ⊓ L = X.1 := (eq_of_fr h7 (by omega)).symm
  refine ⟨pl, hplU, ?_, hXpl, h9⟩
  rw [h9] at h6
  omega

/-- a plane through `X ∈ L` meeting the codimension-two subspace `L` only in `X` -/
theorem exists_plane {L U : Submodule K (Fin N → K)} {X : Lines K N} (hXL : X.1 ≤ L)
    (hLU : L ≤ U) (hdim : Module.finrank K L + 2 = Module.finrank K U) :
    ∃ pl : Submodule K (Fin N → K), pl ≤ U ∧ Module.finrank K pl = 3 ∧ X.1 ≤ pl ∧
      pl ⊓ L = X.1 := by
  obtain ⟨Y1, hY1U, hY1L⟩ := exists_point hLU (by omega)
  have e1 := fr_sup_line L Y1 hY1L
  obtain ⟨Y2, hY2U, hY2L⟩ := exists_point (sup_le hLU hY1U : L ⊔ Y1.1 ≤ U) (by omega)
  have e2 := fr_sup_line (L ⊔ Y1.1) Y2 hY2L
  refine exists_plane_aux hXL hLU hdim hY1U hY2U ?_ ?_
  · have hle : L ⊔ Y1.1 ⊔ Y2.1 ≤ X.1 ⊔ Y1.1 ⊔ Y2.1 ⊔ L := by
      refine sup_le (sup_le ?_ ?_) ?_
      · exact le_sup_right
      · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
      · exact le_sup_of_le_left le_sup_right
    have := fr_mono hle
    omega
  · have a1 := Submodule.finrank_add_le_finrank_add_finrank (X.1 ⊔ Y1.1) Y2.1
    have a2 := Submodule.finrank_add_le_finrank_add_finrank X.1 Y1.1
    rw [X.2, Y1.2] at a2
    rw [Y2.2] at a1
    omega

/-! ## Weight of two-combinations -/
theorem wt_two_le {p : ℕ} (T A B : Submodule K (Fin N → K)) (α β : ZMod p) :
    wt T (α • ind p A + β • ind p B) ≤ (pts (T ⊓ A)).card + (pts (T ⊓ B)).card := by
  classical
  rw [wt_eq]
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro Y hY
  rw [mem_supp] at hY
  rw [Finset.mem_union, mem_pts, mem_pts]
  by_contra h
  push Not at h
  apply hY.2
  have hA : ¬ Y.1 ≤ A := fun h' => h.1 (le_inf hY.1 h')
  have hB : ¬ Y.1 ≤ B := fun h' => h.2 (le_inf hY.1 h')
  simp [ind_nle hA, ind_nle hB]

/-- if a hyperplane `L` of `S` is heavy, it is one of the two hyperplanes of a representation -/
theorem rep_big {p : ℕ} {S L A B : Submodule K (Fin N → K)} {k : ℕ} (hL : IsHyp L S)
    (hA : IsHyp A S) (hB : IsHyp B S) (hLk : Module.finrank K L = k + 1) {α β : ZMod p}
    (hw : 2 * th (Fintype.card K) k < wt L (α • ind p A + β • ind p B)) : A = L ∨ B = L := by
  by_contra h
  push Not at h
  have e1 := hyp_inf hA hL h.1
  have e2 := hyp_inf hB hL h.2
  have := wt_two_le L A B α β
  rw [pts_card' (k := k) (by omega), pts_card' (k := k) (by omega)] at this
  omega

theorem th_le (q k : ℕ) (hq : 2 ≤ q) : th q k ≤ q ^ k := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have h := th_mul r k
  nlinarith

/-! ## THREE: a combination of three hyperplanes -/
open Classical in
theorem excl_card {U H1 H2 H3 : Submodule K (Fin N → K)} {d : ℕ}
    (hd : Module.finrank K U = d + 4) (h1 : IsHyp H1 U) (h2 : IsHyp H2 U) (h3 : IsHyp H3 U)
    (h12 : H1 ≠ H2) (h13 : H1 ≠ H3) :
    Fintype.card K ^ (d + 2) - Fintype.card K ^ (d + 1) ≤
      ((pts H1).filter (fun Y => ¬ (Y.1 ≤ H2 ∨ Y.1 ≤ H3))).card := by
  have hH1 : Module.finrank K H1 = d + 3 := by have := h1.2; omega
  have e2 := hyp_inf h2 h1 (Ne.symm h12)
  have e3 := hyp_inf h3 h1 (Ne.symm h13)
  have hsplit := Finset.card_filter_add_card_filter_not (s := pts H1)
    (fun Y : Lines K N => Y.1 ≤ H2 ∨ Y.1 ≤ H3)
  have hsub : (pts H1).filter (fun Y => Y.1 ≤ H2 ∨ Y.1 ≤ H3) =
      pts (H1 ⊓ H2) ∪ pts (H1 ⊓ H3) := by
    ext Y; simp only [Finset.mem_filter, Finset.mem_union, mem_pts, le_inf_iff]; tauto
  have hunion := Finset.card_union_add_card_inter (pts (H1 ⊓ H2)) (pts (H1 ⊓ H3))
  rw [pts_inter] at hunion
  have hc2 : (pts (H1 ⊓ H2)).card = th (Fintype.card K) (d + 2) := pts_card' (by omega)
  have hc3 : (pts (H1 ⊓ H3)).card = th (Fintype.card K) (d + 2) := pts_card' (by omega)
  have hc1 : (pts H1).card = th (Fintype.card K) (d + 3) := pts_card' hH1
  have htr : d + 1 ≤ Module.finrank K ↥(H1 ⊓ H2 ⊓ (H1 ⊓ H3)) := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (H1 ⊓ H2) (H1 ⊓ H3)
    have := fr_mono (sup_le inf_le_left inf_le_left : H1 ⊓ H2 ⊔ H1 ⊓ H3 ≤ H1)
    omega
  have hct : th (Fintype.card K) (d + 1) ≤ (pts (H1 ⊓ H2 ⊓ (H1 ⊓ H3))).card := by
    rw [pts_card]; exact th_mono _ htr
  rw [hsub] at hsplit
  have t3 : th (Fintype.card K) (d + 3) = th (Fintype.card K) (d + 2) + Fintype.card K ^ (d + 2) :=
    th_succ _ _
  have t2 : th (Fintype.card K) (d + 2) = th (Fintype.card K) (d + 1) + Fintype.card K ^ (d + 1) :=
    th_succ _ _
  have hpow : Fintype.card K ^ (d + 1) ≤ Fintype.card K ^ (d + 2) :=
    Nat.pow_le_pow_right Fintype.card_pos (by omega)
  have := Nat.sub_add_cancel hpow
  omega

theorem three {p : ℕ} {U H1 H2 H3 : Submodule K (Fin N → K)} {d : ℕ}
    (hd : Module.finrank K U = d + 4) (h1 : IsHyp H1 U) (h2 : IsHyp H2 U) (h3 : IsHyp H3 U)
    (α β γ : ZMod p) :
    TwoComb p U (α • ind p H1 + β • ind p H2 + γ • ind p H3) ∨
      3 * (Fintype.card K ^ (d + 2) - Fintype.card K ^ (d + 1)) ≤
        wt U (α • ind p H1 + β • ind p H2 + γ • ind p H3) := by
  classical
  by_cases hα : α = 0
  · left; exact ⟨H2, H3, h2, h3, β, γ, by simp [hα]⟩
  by_cases hβ : β = 0
  · left; exact ⟨H1, H3, h1, h3, α, γ, by simp [hβ]⟩
  by_cases hγ : γ = 0
  · left; exact ⟨H1, H2, h1, h2, α, β, by simp [hγ]⟩
  by_cases h12 : H1 = H2
  · left; subst h12; exact ⟨H1, H3, h1, h3, α + β, γ, by rw [add_smul]⟩
  by_cases h13 : H1 = H3
  · left; subst h13; exact ⟨H1, H2, h1, h2, α + γ, β, by rw [add_smul]; abel⟩
  by_cases h23 : H2 = H3
  · left; subst h23; exact ⟨H1, H2, h1, h2, α, β + γ, by rw [add_smul, add_assoc]⟩
  right
  have E1 := excl_card hd h1 h2 h3 h12 h13
  have E2 := excl_card hd h2 h1 h3 (Ne.symm h12) h23
  have E3 := excl_card hd h3 h1 h2 (Ne.symm h13) (Ne.symm h23)
  set F1 := (pts H1).filter (fun Y => ¬ (Y.1 ≤ H2 ∨ Y.1 ≤ H3)) with hF1
  set F2 := (pts H2).filter (fun Y => ¬ (Y.1 ≤ H1 ∨ Y.1 ≤ H3)) with hF2
  set F3 := (pts H3).filter (fun Y => ¬ (Y.1 ≤ H1 ∨ Y.1 ≤ H2)) with hF3
  have hval : ∀ Y : Lines K N, (α • ind p H1 + β • ind p H2 + γ • ind p H3) Y =
      α * ind p H1 Y + β * ind p H2 Y + γ * ind p H3 Y := by intro Y; simp
  have hd12 : Disjoint F1 F2 := by
    rw [Finset.disjoint_left]; intro Y hY1 hY2
    simp only [hF1, hF2, Finset.mem_filter, mem_pts] at hY1 hY2
    exact hY1.2 (Or.inl hY2.1)
  have hd13 : Disjoint F1 F3 := by
    rw [Finset.disjoint_left]; intro Y hY1 hY3
    simp only [hF1, hF3, Finset.mem_filter, mem_pts] at hY1 hY3
    exact hY1.2 (Or.inr hY3.1)
  have hd23 : Disjoint F2 F3 := by
    rw [Finset.disjoint_left]; intro Y hY2 hY3
    simp only [hF2, hF3, Finset.mem_filter, mem_pts] at hY2 hY3
    exact hY2.2 (Or.inr hY3.1)
  have hsub : F1 ∪ F2 ∪ F3 ⊆ supp U (α • ind p H1 + β • ind p H2 + γ • ind p H3) := by
    intro Y hY
    rw [mem_supp, hval]
    simp only [Finset.mem_union, hF1, hF2, hF3, Finset.mem_filter, mem_pts, not_or] at hY
    rcases hY with (⟨hY1, hY2, hY3⟩ | ⟨hY2, hY1, hY3⟩) | ⟨hY3, hY1, hY2⟩
    · refine ⟨hY1.trans h1.1, ?_⟩
      rw [ind_le hY1, ind_nle hY2, ind_nle hY3]; simpa using hα
    · refine ⟨hY2.trans h2.1, ?_⟩
      rw [ind_le hY2, ind_nle hY1, ind_nle hY3]; simpa using hβ
    · refine ⟨hY3.trans h3.1, ?_⟩
      rw [ind_le hY3, ind_nle hY1, ind_nle hY2]; simpa using hγ
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩),
    Finset.card_union_of_disjoint hd12] at hcard
  rw [wt_eq]
  omega

/-! ## Case II: a hyperplane with its holes in a hyperplane -/
theorem caseII_step {p : ℕ} [Fact p.Prime] {U P1 Hh : Submodule K (Fin N → K)} {d : ℕ}
    (hpq : p ≤ Fintype.card K) (hd : Module.finrank K U = d + 4)
    (hP1 : IsHyp P1 U) (hHh : IsHyp Hh P1) {c : Lines K N → ZMod p}
    (hho : ∀ ℓ ∈ pts P1, c ℓ = 0 → ℓ.1 ≤ Hh) :
    ∃ α : ZMod p, wt U (c - α • ind p P1) < wt U c := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hP1d : Module.finrank K P1 = d + 3 := by have := hP1.2; omega
  have hHhd : Module.finrank K Hh = d + 2 := by have := hHh.2; omega
  set Hol := (pts P1).filter (fun Y => c Y = 0) with hHol_def
  have hHol : Hol.card ≤ th (Fintype.card K) (d + 2) := by
    rw [← pts_card' hHhd]; apply Finset.card_le_card; intro Y hY
    simp only [hHol_def, Finset.mem_filter] at hY; rw [mem_pts]; exact hho Y hY.1 hY.2
  obtain ⟨α, hα⟩ : ∃ α : ZMod p, Hol.card < ((pts P1).filter (fun Y => c Y = α)).card := by
    by_contra h
    push Not at h
    have hfib := Finset.card_eq_sum_card_fiberwise (f := c) (s := pts P1)
      (t := Finset.univ) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    have hle : (pts P1).card ≤ Fintype.card (ZMod p) * Hol.card := by
      rw [hfib]
      have := Finset.sum_le_card_nsmul Finset.univ
        (fun b => ((pts P1).filter (fun Y => c Y = b)).card) Hol.card (fun b _ => h b)
      rw [Finset.card_univ, smul_eq_mul] at this
      exact this
    rw [ZMod.card, pts_card' hP1d, th_rec] at hle
    have : p * Hol.card ≤ Fintype.card K * th (Fintype.card K) (d + 2) := Nat.mul_le_mul hpq hHol
    omega
  refine ⟨α, ?_⟩
  set Fa := (pts P1).filter (fun Y => c Y = α) with hFa
  have hval : ∀ Y : Lines K N, (c - α • ind p P1) Y = c Y - α * ind p P1 Y := by
    intro Y; simp
  have heq : supp U (c - α • ind p P1) ∪ Fa = supp U c ∪ Hol := by
    ext Y
    simp only [Finset.mem_union, mem_supp, hFa, hHol_def, Finset.mem_filter, mem_pts, hval]
    by_cases hY : Y.1 ≤ P1
    · rw [ind_le hY, mul_one, sub_ne_zero]
      have := hY.trans hP1.1
      tauto
    · rw [ind_nle hY, mul_zero, sub_zero]; simp [hY]
  have hd1 : Disjoint (supp U (c - α • ind p P1)) Fa := by
    rw [Finset.disjoint_left]; intro Y h1 h2
    rw [mem_supp, hval] at h1; simp only [hFa, Finset.mem_filter, mem_pts] at h2
    rw [ind_le h2.1, h2.2] at h1; simp at h1
  have hd2 : Disjoint (supp U c) Hol := by
    rw [Finset.disjoint_left]; intro Y h1 h2
    rw [mem_supp] at h1; simp only [hHol_def, Finset.mem_filter] at h2; exact h1.2 h2.2
  have := congrArg Finset.card heq
  rw [Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2] at this
  rw [wt_eq, wt_eq]
  omega

/-! ## Case I: every hyperplane restriction is a two-combination -/
theorem val_off {p : ℕ} {S L B : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
    {α β : ZMod p} (hrep : res S c = α • ind p L + β • ind p B) (hLS : L ≤ S) {Y : Lines K N}
    (hYL : Y.1 ≤ L) (hYB : ¬ Y.1 ≤ B) : c Y = α := by
  rw [val2 hrep (hYL.trans hLS), ind_le hYL, ind_nle hYB]; ring

open Classical in
theorem card_off {L B : Submodule K (Fin N → K)} {k : ℕ} (hL : Module.finrank K L = k + 2)
    (hLB : Module.finrank K ↥(L ⊓ B) = k + 1) :
    ((pts L).filter (fun Y => ¬ Y.1 ≤ B)).card = Fintype.card K ^ (k + 1) := by
  have h := Finset.card_filter_add_card_filter_not (s := pts L) (fun Y : Lines K N => Y.1 ≤ B)
  have e : (pts L).filter (fun Y => Y.1 ≤ B) = pts (L ⊓ B) := by
    ext Y; simp [mem_pts]
  have t : th (Fintype.card K) (k + 2) = th (Fintype.card K) (k + 1) + Fintype.card K ^ (k + 1) :=
    th_succ _ _
  rw [e, pts_card' hLB, pts_card' hL] at h
  omega

/-- a point of the heavy hyperplane `L` (of `S`) whose value is the value of all but `θ(k+1)`
points of `L`, in the normalized representation `α 1_L + β 1_B` -/
theorem good_point' {p : ℕ} {S L B : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
    {α β : ZMod p} {k : ℕ} (hq : 3 ≤ Fintype.card K) (hLS : IsHyp L S) (hB : IsHyp B S)
    (hrep : res S c = α • ind p L + β • ind p B) (hLk : Module.finrank K L = k + 2)
    (hw : Fintype.card K ^ (k + 1) ≤ wt L c) :
    ∃ X : Lines K N, X.1 ≤ L ∧ c X ≠ 0 ∧
      ((pts L).filter (fun Y => c Y ≠ c X)).card ≤ th (Fintype.card K) (k + 1) := by
  classical
  by_cases hBL : B = L
  · subst hBL
    have hpos : 0 < wt B c := lt_of_lt_of_le (pow_pos (by omega) _) hw
    rw [wt_eq] at hpos
    obtain ⟨X, hX⟩ := Finset.card_pos.mp hpos
    rw [mem_supp] at hX
    refine ⟨X, hX.1, hX.2, ?_⟩
    have : (pts B).filter (fun Y => c Y ≠ c X) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro Y hY; rw [mem_pts] at hY
      rw [val2 hrep (hY.trans hLS.1), val2 hrep (hX.1.trans hLS.1), ind_le hY, ind_le hX.1]
      simp
    rw [this]; simp
  · have hLB := hyp_inf hB hLS hBL
    have hoff := card_off (k := k) (B := B) hLk (by omega)
    have hcnt : ((pts L).filter (fun Y => c Y ≠ α)).card ≤ th (Fintype.card K) (k + 1) := by
      rw [← pts_card' (U := L ⊓ B) (by omega)]
      apply Finset.card_le_card; intro Y hY
      simp only [Finset.mem_filter, mem_pts] at hY ⊢
      refine le_inf hY.1 ?_
      by_contra hYB; exact hY.2 (val_off hrep hLS.1 hY.1 hYB)
    have hα : α ≠ 0 := by
      intro h0
      have : wt L c ≤ th (Fintype.card K) (k + 1) := by
        rw [wt_eq]; refine le_trans (Finset.card_le_card ?_) hcnt
        intro Y hY; rw [mem_supp] at hY; simp only [Finset.mem_filter, mem_pts]
        exact ⟨hY.1, by rw [h0]; exact hY.2⟩
      have := two_th_lt (Fintype.card K) (k + 1) hq (by omega); omega
    have hpos : 0 < ((pts L).filter (fun Y => ¬ Y.1 ≤ B)).card := by
      rw [hoff]; exact pow_pos (by omega) _
    obtain ⟨X, hX⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, mem_pts] at hX
    have hcX := val_off hrep hLS.1 hX.1 hX.2
    exact ⟨X, hX.1, by rw [hcX]; exact hα, by rw [hcX]; exact hcnt⟩

theorem good_point {p : ℕ} {S L A B : Submodule K (Fin N → K)} {c : Lines K N → ZMod p}
    {α β : ZMod p} {k : ℕ} (hq : 3 ≤ Fintype.card K) (hLS : IsHyp L S) (hA : IsHyp A S)
    (hB : IsHyp B S) (hrep : res S c = α • ind p A + β • ind p B)
    (hLk : Module.finrank K L = k + 2) (hw : Fintype.card K ^ (k + 1) ≤ wt L c) :
    ∃ X : Lines K N, X.1 ≤ L ∧ c X ≠ 0 ∧
      ((pts L).filter (fun Y => c Y ≠ c X)).card ≤ th (Fintype.card K) (k + 1) := by
  have hw' : 2 * th (Fintype.card K) (k + 1) < wt L (α • ind p A + β • ind p B) := by
    rw [← hrep, wt_res L S hLS.1]
    have := two_th_lt (Fintype.card K) (k + 1) hq (by omega); omega
  rcases rep_big (k := k + 1) hLS hA hB (by omega) hw' with h | h
  · subst h; exact good_point' hq hLS hB hrep hLk hw
  · subst h; exact good_point' hq hLS hA (by rw [hrep, add_comm]) hLk hw

/-- through a good point `X` of `L`, a line `l` meeting `L` only in `X` is at most a 2-secant -/
theorem caseI_line {p : ℕ} {S L B l : Submodule K (Fin N → K)} {X : Lines K N}
    {c : Lines K N → ZMod p} {α β : ZMod p} {k : ℕ} (hq : 3 ≤ Fintype.card K)
    (hLS : IsHyp L S) (hB : IsHyp B S) (hlS : l ≤ S) (hl : Module.finrank K l = 2)
    (hXl : X.1 ≤ l) (hXL : X.1 ≤ L) (hlL : l ⊓ L ≤ X.1)
    (hrep : res S c = α • ind p L + β • ind p B) (hLk : Module.finrank K L = k + 2)
    (hgood : ((pts L).filter (fun Y => c Y ≠ c X)).card ≤ th (Fintype.card K) (k + 1)) :
    wt l c ≤ 2 := by
  classical
  have hX1 := X.2
  have hpt : ∀ Y : Lines K N, Y.1 ≤ l → Y.1 ≤ L → Y = X :=
    fun Y h1 h2 => line_eq_of_le ((le_inf h1 h2).trans hlL)
  have hlnL : ¬ l ≤ L := by
    intro h; have := fr_mono ((le_inf le_rfl h).trans hlL); omega
  by_cases hlB : l ≤ B
  · by_cases hβ : β = 0
    · rw [wt_eq]
      have : supp l c ⊆ {X} := by
        intro Y hY; rw [mem_supp] at hY; rw [Finset.mem_singleton]
        by_cases hYL : Y.1 ≤ L
        · exact hpt Y hY.1 hYL
        · exfalso; apply hY.2; rw [val2 hrep (hY.1.trans hlS), ind_nle hYL, hβ]; ring
      have := Finset.card_le_card this; simp at this; omega
    · exfalso
      have hBL : B ≠ L := by rintro rfl; exact hlnL hlB
      have hLB := hyp_inf hB hLS hBL
      have hoff := card_off (k := k) (B := B) hLk (by omega)
      have hXB : X.1 ≤ B := hXl.trans hlB
      have hcX : c X = α + β := by
        rw [val2 hrep (hXL.trans hLS.1), ind_le hXL, ind_le hXB]; ring
      have hsub : (pts L).filter (fun Y => ¬ Y.1 ≤ B) ⊆
          (pts L).filter (fun Y => c Y ≠ c X) := by
        intro Y hY; simp only [Finset.mem_filter, mem_pts] at hY ⊢
        refine ⟨hY.1, ?_⟩
        rw [val_off hrep hLS.1 hY.1 hY.2, hcX]
        intro h; apply hβ; linear_combination -h
      have := Finset.card_le_card hsub
      have := two_th_lt (Fintype.card K) (k + 1) hq (by omega)
      omega
  · rw [wt_eq]
    have hsub : supp l c ⊆ insert X (pts (l ⊓ B)) := by
      intro Y hY; rw [mem_supp] at hY; rw [Finset.mem_insert, mem_pts]
      by_cases hYL : Y.1 ≤ L
      · exact Or.inl (hpt Y hY.1 hYL)
      · right; refine le_inf hY.1 ?_
        by_contra hYB; apply hY.2
        rw [val2 hrep (hY.1.trans hlS), ind_nle hYL, ind_nle hYB]; ring
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have h2 : Module.finrank K ↥(l ⊓ B) ≤ 1 := by
      have hlt : l ⊓ B < l :=
        lt_of_le_of_ne inf_le_left (fun h => hlB (by rw [← h]; exact inf_le_right))
      have := Submodule.finrank_lt_finrank_of_lt hlt; omega
    rw [pts_card] at h1
    have := th_mono (Fintype.card K) h2
    rw [th_one] at this
    omega

theorem caseI_line_any {p : ℕ} {S L A B l : Submodule K (Fin N → K)} {X : Lines K N}
    {c : Lines K N → ZMod p} {α β : ZMod p} {k : ℕ} (hq : 3 ≤ Fintype.card K)
    (hLS : IsHyp L S) (hA : IsHyp A S) (hB : IsHyp B S) (hlS : l ≤ S)
    (hl : Module.finrank K l = 2) (hXl : X.1 ≤ l) (hXL : X.1 ≤ L) (hlL : l ⊓ L ≤ X.1)
    (hrep : res S c = α • ind p A + β • ind p B) (hLk : Module.finrank K L = k + 2)
    (hw : Fintype.card K ^ (k + 1) ≤ wt L c)
    (hgood : ((pts L).filter (fun Y => c Y ≠ c X)).card ≤ th (Fintype.card K) (k + 1)) :
    wt l c ≤ 2 := by
  have hw' : 2 * th (Fintype.card K) (k + 1) < wt L (α • ind p A + β • ind p B) := by
    rw [← hrep, wt_res L S hLS.1]
    have := two_th_lt (Fintype.card K) (k + 1) hq (by omega); omega
  rcases rep_big (k := k + 1) hLS hA hB (by omega) hw' with h | h
  · subst h; exact caseI_line hq hLS hB hlS hl hXl hXL hlL hrep hLk hgood
  · subst h; exact caseI_line hq hLS hA hlS hl hXl hXL hlL (by rw [hrep, add_comm]) hLk hgood

/-- Case I: if the restriction to every hyperplane is a two-combination, then `c = 0` -/
theorem caseI (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)} {d : ℕ}
    (hq : 7 ≤ Fintype.card K) (hd : Module.finrank K U = d + 4) {c : Lines K N → ZMod p}
    (hc : c ∈ Code p U) (htc : ∀ Hp, IsHyp Hp U → TwoComb p Hp (res Hp c)) :
    ∀ X : Lines K N, c X = 0 := by
  intro X0
  by_contra hX0
  have hX0U : X0.1 ≤ U := by
    by_contra h; exact hX0 (code_eq_zero hc h)
  have hcard := hyps_card hX0U
  rw [X0.2, hd, show d + 4 - 1 = (d + 2) + 1 by omega, th_succ] at hcard
  have hpos : 0 < (hyps X0.1 U).card := by rw [hcard]; positivity
  obtain ⟨P0, hP0⟩ := Finset.card_pos.mp hpos
  rw [mem_hyps] at hP0
  have hP0d : Module.finrank K P0 = d + 3 := by have := hP0.1.2; omega
  obtain ⟨A', B', hA', hB', α', β', hrep0⟩ := htc P0 hP0.1
  obtain ⟨L, hL, hX0L, hwL⟩ := twoComb_long (htc P0 hP0.1) (by omega) hP0.2
    (by rw [res_le hP0.2]; exact hX0)
  rw [wt_res L P0 hL.1, hP0d, show d + 3 - 2 = d + 1 by omega] at hwL
  have hLd : Module.finrank K L = d + 2 := by have := hL.2; omega
  obtain ⟨X, hXL, hcX, hgood⟩ := good_point (k := d) (by omega) hL hA' hB' hrep0 hLd hwL
  have hLU : L ≤ U := hL.1.trans hP0.1.1
  obtain ⟨pl, hplU, hpl3, hXpl, hplL⟩ := exists_plane hXL hLU (by omega)
  have hline : ∀ l : Submodule K (Fin N → K), l ≤ pl → Module.finrank K l = 2 → X.1 ≤ l →
      wt l c ≤ 2 := by
    intro l hlpl hl hXl
    have hlL : l ⊓ L ≤ X.1 := (inf_le_inf_right L hlpl).trans hplL.le
    have hLl : L ⊓ l = X.1 := le_antisymm (by rw [inf_comm]; exact hlL) (le_inf hXL hXl)
    have hfr := Submodule.finrank_sup_add_finrank_inf_eq L l
    rw [hLl, X.2] at hfr
    have hSU : L ⊔ l ≤ U := sup_le hLU (hlpl.trans hplU)
    have hS : IsHyp (L ⊔ l) U := ⟨hSU, by omega⟩
    obtain ⟨A, B, hA, hB, α, β, hrep⟩ := htc _ hS
    exact caseI_line_any (k := d) (by omega) ⟨le_sup_left, by omega⟩ hA hB le_sup_right hl hXl
      hXL hlL hrep hLd hwL hgood
  have hpart := ext_partition hXpl c
  have hext := ext_card hXpl
  rw [hpl3, X.2, show 3 - 1 = 1 + 1 by rfl, th_succ, th_one, pow_one] at hext
  have hX1 : wt X.1 c = 1 := by
    rw [wt_eq, Finset.card_eq_one]
    refine ⟨X, ?_⟩
    ext Y; rw [mem_supp, Finset.mem_singleton]
    constructor
    · rintro ⟨h, _⟩; exact line_eq_of_le h
    · rintro rfl; exact ⟨le_rfl, hcX⟩
  have hsum : ∑ V ∈ ext X.1 pl, wt V c ≤ (ext X.1 pl).card • 2 :=
    Finset.sum_le_card_nsmul (ext X.1 pl) (fun V => wt V c) 2 (fun V hV => by
      rw [mem_ext] at hV; exact hline V hV.2.1 (by rw [hV.2.2, X.2]) hV.1)
  rw [smul_eq_mul, hext] at hsum
  rw [hX1, hext] at hpart
  have hwpl : wt pl c ≤ Fintype.card K + 2 := by omega
  have hres : res pl c ∈ Code p pl := res_mem p a hG hc hplU (by omega)
  have hwres : wt pl (res pl c) = wt pl c := wt_res pl pl le_rfl c
  have htcpl := P1 p a hG hpl3 hres (by omega)
  obtain ⟨L', hL', hXL', hwL'⟩ := twoComb_long htcpl (by omega) hXpl
    (by rw [res_le hXpl]; exact hcX)
  rw [wt_res L' pl hL'.1, hpl3, show 3 - 2 = 1 by rfl, pow_one] at hwL'
  have := hline L' hL'.1 (by have := hL'.2; omega) hXL'
  omega

/-! ## The theorem -/
theorem T_main (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hD : 4 ≤ Module.finrank K U)
    (hIH : ∀ Hp : Submodule K (Fin N → K), IsHyp Hp U → ∀ c' ∈ Code p Hp,
      wt Hp c' ≤ Wb (Fintype.card K) (Module.finrank K U - 1) → TwoComb p Hp c')
    (hlines : ∀ c ∈ Code p U, wt U c ≤ Wb (Fintype.card K) (Module.finrank K U) →
      ∀ L : Submodule K (Fin N → K), L ≤ U → Module.finrank K L = 2 →
        wt L c ≤ 2 ∨ Fintype.card K ≤ wt L c)
    {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (hw : wt U c ≤ Wb (Fintype.card K) (Module.finrank K U)) : TwoComb p U c := by
  obtain ⟨d, hd⟩ : ∃ d, Module.finrank K U = d + 4 := ⟨_, (Nat.sub_add_cancel hD).symm⟩
  have hq : 32 < Fintype.card K := by rw [hG.1]; exact hG.2.1
  have hpq : p ≤ Fintype.card K := by
    rw [hG.1]; apply Nat.le_self_pow; rintro rfl; have := hG.2.1; simp at this
  rw [hd] at hIH hlines hw
  rw [show d + 4 - 1 = d + 3 by omega] at hIH
  have hWb4 : Wb (Fintype.card K) (d + 4) =
      3 * Fintype.card K ^ (d + 2) - 3 * Fintype.card K ^ (d + 1) - 1 := by
    simp only [Wb, show d + 4 - 2 = d + 2 by omega, show d + 4 - 3 = d + 1 by omega]
  have hWb3 : Wb (Fintype.card K) (d + 3) =
      3 * Fintype.card K ^ (d + 1) - 3 * Fintype.card K ^ d - 1 := by
    simp only [Wb, show d + 3 - 2 = d + 1 by omega, show d + 3 - 3 = d by omega]
  suffices H : ∀ n, ∀ c ∈ Code p U, wt U c = n → wt U c ≤ Wb (Fintype.card K) (d + 4) →
      TwoComb p U c from H _ c hc rfl hw
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hc hn hw
  by_cases hII : ∃ P1, IsHyp P1 U ∧ ∃ Hh, IsHyp Hh P1 ∧ ∀ ℓ ∈ pts P1, c ℓ = 0 → ℓ.1 ≤ Hh
  · obtain ⟨P1, hP1, Hh, hHh, hho⟩ := hII
    obtain ⟨α, hlt⟩ := caseII_step hpq hd hP1 hHh hho
    have hmem : ind p P1 ∈ Code p U := Submodule.subset_span ⟨P1, hP1, rfl⟩
    have hc' : c - α • ind p P1 ∈ Code p U := Submodule.sub_mem _ hc (Submodule.smul_mem _ α hmem)
    obtain ⟨B, C, hB, hC, β, γ, hrep⟩ := ih _ (by omega) _ hc' rfl (by omega)
    have hceq : c = α • ind p P1 + β • ind p B + γ • ind p C := by
      rw [add_assoc, ← hrep]; abel
    rcases three hd hP1 hB hC α β γ with h | h
    · rw [hceq]; exact h
    · exfalso
      rw [← hceq] at h
      have hpow : Fintype.card K ^ (d + 1) ≤ Fintype.card K ^ (d + 2) :=
        Nat.pow_le_pow_right Fintype.card_pos (by omega)
      omega
  · push Not at hII
    have htc : ∀ Hp, IsHyp Hp U → TwoComb p Hp (res Hp c) := by
      intro Hp hHp
      have hHpd : Module.finrank K Hp = d + 3 := by have := hHp.2; omega
      have hsmall : wt Hp c ≤ 2 * Fintype.card K ^ (d + 1) + th (Fintype.card K) (d + 1) := by
        rcases K_class (by omega) c (T := Hp) (by omega)
            (fun L hL hL2 => hlines c hc hw L (hL.trans hHp.1) hL2) with h | ⟨Hh, hHh, hho⟩
        · rw [hHpd, show d + 3 - 2 = d + 1 by omega] at h; exact h
        · obtain ⟨ℓ, hℓ, h0, hn'⟩ := hII Hp hHp Hh hHh
          exact absurd (hho ℓ hℓ h0) hn'
      apply hIH Hp hHp _ (res_mem p a hG hc hHp.1 (by omega))
      rw [wt_res Hp Hp le_rfl, hWb3]
      have h1 : th (Fintype.card K) (d + 1) = th (Fintype.card K) d + Fintype.card K ^ d :=
        th_succ _ _
      have h2 := th_le (Fintype.card K) d (by omega)
      have h3 : 33 * Fintype.card K ^ d ≤ Fintype.card K ^ (d + 1) := by
        have := Nat.mul_le_mul_right (Fintype.card K ^ d) (show 33 ≤ Fintype.card K by omega)
        rw [pow_succ, mul_comm (Fintype.card K ^ d)]; exact this
      have h4 : 1 ≤ Fintype.card K ^ d := Nat.one_le_pow _ _ (by omega)
      omega
    have h0 := caseI p a hG (by omega) hd hc htc
    have hc0 : c = 0 := funext h0
    have hcard := hyps_card (bot_le : (⊥ : Submodule K (Fin N → K)) ≤ U)
    rw [finrank_bot, hd, Nat.sub_zero, th_succ] at hcard
    have hpos : 0 < (hyps ⊥ U).card := by rw [hcard]; positivity
    obtain ⟨H, hH⟩ := Finset.card_pos.mp hpos
    rw [mem_hyps] at hH
    exact ⟨H, H, hH.1, hH.1, 0, 0, by simp [hc0]⟩

end ProxGapTight.Dev.Q366.PartT
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366
open ProxGapTight
variable {K : Type} [Field K] [Fintype K] {N : ℕ}
/-! ## Part T: two hyperplanes (ADSW Theorem 3.2.6, by induction on the weight) -/
alias T_main := ProxGapTight.Dev.Q366.PartT.T_main

/-! ## Assembly -/
theorem lines2 (p a : ℕ) [Fact p.Prime] (hG : Good p a K) {U : Submodule K (Fin N → K)}
    (hD : 4 ≤ Module.finrank K U) {c : Lines K N → ZMod p} (hc : c ∈ Code p U)
    (hw : wt U c ≤ Wb (Fintype.card K) (Module.finrank K U))
    {L : Submodule K (Fin N → K)} (hLU : L ≤ U) (hL : Module.finrank K L = 2) :
    wt L c ≤ 2 ∨ Fintype.card K ≤ wt L c := by
  rcases A_lines p a hG hD hc hw hLU hL with h | h
  · rcases Nat.lt_or_ge (wt L c) 3 with h' | h'
    · left; omega
    · have h3 : wt L c = 3 := by omega
      have := G_main p a hG (by omega) hc hLU hL h3
      omega
  · have hne := C_lines p a hG hD hc hw hLU hL
    right; omega

theorem leafI (p a : ℕ) [Fact p.Prime] (hG : Good p a K) :
    ∀ D : ℕ, 3 ≤ D → ∀ U : Submodule K (Fin N → K), Module.finrank K U = D →
      ∀ c ∈ Code p U, wt U c ≤ Wb (Fintype.card K) D → TwoComb p U c := by
  intro D hD
  induction D, hD using Nat.le_induction with
  | base =>
    intro U hU c hc hw
    refine P1 p a hG hU hc ?_
    have : Wb (Fintype.card K) 3 = 3 * Fintype.card K - 4 := by
      simp only [Wb]; norm_num; omega
    omega
  | succ D hD ih =>
    intro U hU c hc hw
    refine T_main p a hG (by omega) ?_ ?_ hc (by rw [hU]; exact hw)
    · intro Hp hHp c' hc' hw'
      exact ih Hp (by have := hHp.2; omega) c' hc' (by rw [hU] at hw'; simpa using hw')
    · intro c₁ hc₁ hw₁ L hLU hL
      exact lines2 p a hG (by omega) hc₁ hw₁ hLU hL

end ProxGapTight.Dev.Q366
end

section
set_option autoImplicit false
namespace ProxGapTight.Dev.Q366.PartFin
open ProxGapTight ProxGapTight.Dev.Q366
theorem chk_ad21_result_3_3_hyperplanes (p a : ℕ) [Fact p.Prime] (hQ : 32 < p ^ a)
    (h49 : p ^ a ≠ 49) (h121 : p ^ a ≠ 121) (d : ℕ) (hd : 3 ≤ d)
    (K : Type) [Field K] [Fintype K] (hK : Fintype.card K = p ^ a)
    (v : Lines K d → ZMod p)
    (hv : v ∈ Submodule.span (ZMod p) (Set.range fun H :
        {H : Submodule K (Fin d → K) // Module.finrank K H + 1 = d} =>
          Set.indicator {ℓ : Lines K d | ℓ.1 ≤ H.1} (fun _ => (1 : ZMod p))))
    (hw : hammingNorm v ≤ 3 * (p ^ a) ^ (d - 2) - 3 * (p ^ a) ^ (d - 3) - 1) :
    ∃ H H' : {H : Submodule K (Fin d → K) // Module.finrank K H + 1 = d}, ∃ α β : ZMod p,
      v = α • Set.indicator {ℓ : Lines K d | ℓ.1 ≤ H.1} (fun _ => (1 : ZMod p)) +
        β • Set.indicator {ℓ : Lines K d | ℓ.1 ≤ H'.1} (fun _ => (1 : ZMod p)) := by
  classical
  have hG : Good p a K := ⟨hK, hQ, h49, h121⟩
  have htop : Module.finrank K (⊤ : Submodule K (Fin d → K)) = d := by
    rw [finrank_top, Module.finrank_fin_fun]
  have hset : (Set.range fun H :
        {H : Submodule K (Fin d → K) // Module.finrank K H + 1 = d} =>
          Set.indicator {ℓ : Lines K d | ℓ.1 ≤ H.1} (fun _ => (1 : ZMod p))) =
      {f | ∃ W, IsHyp W (⊤ : Submodule K (Fin d → K)) ∧ f = ind p W} := by
    ext f
    simp only [Set.mem_range, IsHyp, htop, le_top, true_and, ind]
    constructor
    · rintro ⟨H, rfl⟩; exact ⟨H.1, H.2, rfl⟩
    · rintro ⟨W, hW, rfl⟩; exact ⟨⟨W, hW⟩, rfl⟩
  have hc : v ∈ Code p (⊤ : Submodule K (Fin d → K)) := by
    unfold Code; rw [← hset]; exact hv
  have hwt : wt (⊤ : Submodule K (Fin d → K)) v = hammingNorm v := by
    unfold wt hammingNorm pts
    congr 1
    ext ℓ
    simp
  have hw' : wt (⊤ : Submodule K (Fin d → K)) v ≤ Wb (Fintype.card K) d := by
    rw [hwt, hK]; exact hw
  obtain ⟨A, B, hA, hB, α, β, h⟩ := leafI p a hG d hd ⊤ htop v hc hw'
  refine ⟨⟨A, hA.2.trans htop⟩, ⟨B, hB.2.trans htop⟩, α, β, ?_⟩
  rw [h]
  rfl

end ProxGapTight.Dev.Q366.PartFin
end

theorem solution : type_of% @ProxGapTight.Dev.Q366.PartFin.chk_ad21_result_3_3_hyperplanes :=
  @ProxGapTight.Dev.Q366.PartFin.chk_ad21_result_3_3_hyperplanes
