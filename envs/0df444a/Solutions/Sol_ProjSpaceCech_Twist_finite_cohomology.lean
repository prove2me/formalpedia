-- Prove2me | solution 1 for ProjSpaceCech.Twist.finite_cohomology
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/586a1a94-fde5-54cd-9f9a-0506eac769fe

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ProjSpaceCech_Twist_finite_cohomology

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

universe u

noncomputable section

open Finset Function

namespace ProjSpaceCech
p2m_export "ProjSpaceCech" "Twist.MonExp Twist.negSupp Twist.mem_negSupp Twist.Mon Twist.Mon.incl Twist.Mon.incl_injective Twist.Sec Idx Idx.img Idx.card_img Idx.face Idx.img_face_subset Twist.faceRes Twist.cochain Twist.d Twist.d_apply Twist.cochain_subsingleton_of_lt Twist.H"
p2m_open "ProjSpaceCech"

section Cohomology

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

namespace Twist p2m_export "ProjSpaceCech.Twist" "MonExp negSupp mem_negSupp Mon Mon.incl Mon.incl_injective Sec faceRes cochain d d_apply cochain_subsingleton_of_lt H" end Twist
p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.subsingleton_cohomology_of_lt {i : ℕ} (hi : n < i) :
    Subsingleton (Twist.H R n d i) := by
  rcases i with _ | j
  · exact absurd hi (Nat.not_lt_zero n)
  dsimp only [Twist.H]
  have hsub := Twist.cochain_subsingleton_of_lt R n d hi
  exact ⟨fun x y => Quotient.inductionOn₂' x y fun a b =>
    congrArg _ (Subtype.ext (hsub.elim a.1 b.1))⟩

end Cohomology

section Homotopy

variable {n : ℕ}

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.idx_canonical {i : ℕ} (s : Idx n i) :
    s.1 = (Idx.img n s).orderEmbOfFin (Idx.card_img n s) :=
  Finset.orderEmbOfFin_unique _ (fun k => Finset.mem_image_of_mem _ (Finset.mem_univ k)) s.2

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.idx_eq_of_img {i : ℕ} {s t : Idx n i}
    (h : Idx.img n s = Idx.img n t) : s = t := by
  apply Subtype.ext
  rw [Twist.idx_canonical s]
  exact (Finset.orderEmbOfFin_unique (Idx.card_img n s)
    (fun k => h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ k)) t.2).symm

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.img_face {i : ℕ} (s : Idx n (i + 1))
    (j : Fin (i + 2)) :
    Idx.img n (Idx.face n s j)
      = (Idx.img n s).erase (s.1 j) := by
  ext x
  simp only [Idx.img, Idx.face, mem_image, mem_univ, true_and,
    mem_erase, Function.comp_apply]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨s.2.injective.ne (Fin.succAbove_ne j k), Fin.succAbove j k, rfl⟩
  · rintro ⟨hne, k, rfl⟩
    obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq (fun h => hne (congrArg s.1 h))
    exact ⟨k', rfl⟩

p2m_open_scoped "ProjSpaceCech.Twist" in

def Twist.altOfFinset {i : ℕ} (T : Finset (Fin (n + 1))) (hT : T.card = i + 1) :
    Idx n i :=
  ⟨T.orderEmbOfFin hT, (T.orderEmbOfFin hT).strictMono⟩

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.img_altOfFinset {i : ℕ} (T : Finset (Fin (n + 1)))
    (hT : T.card = i + 1) :
    Idx.img n (Twist.altOfFinset T hT) = T := by
  simp only [Idx.img, Twist.altOfFinset]
  exact Finset.image_orderEmbOfFin_univ T hT

p2m_open_scoped "ProjSpaceCech.Twist" in

def Twist.altPos {i : ℕ} (s : Idx n i) (j : Fin (n + 1))
    (hj : j ∈ Idx.img n s) : Fin (i + 1) :=
  ((Idx.img n s).orderIsoOfFin (Idx.card_img n s)).symm ⟨j, hj⟩

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.idx_val_altPos {i : ℕ} (s : Idx n i)
    (j : Fin (n + 1)) (hj : j ∈ Idx.img n s) :
    s.1 (Twist.altPos s j hj) = j := by
  rw [Twist.idx_canonical s, ← Finset.coe_orderIsoOfFin_apply,
    Twist.altPos, OrderIso.apply_symm_apply]

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.altPos_val {i : ℕ} (s : Idx n i) (p : Fin (i + 1)) :
    Twist.altPos s (s.1 p) (Finset.mem_image_of_mem _ (Finset.mem_univ p)) = p :=
  s.2.injective (Twist.idx_val_altPos s (s.1 p) _)

p2m_open_scoped "ProjSpaceCech.Twist" in

def Twist.altInsert {i : ℕ} (s : Idx n i) (j : Fin (n + 1))
    (hj : j ∉ Idx.img n s) : Idx n (i + 1) :=
  Twist.altOfFinset (insert j (Idx.img n s))
    (by rw [Finset.card_insert_of_notMem hj, Idx.card_img])

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.img_altInsert {i : ℕ} (s : Idx n i)
    (j : Fin (n + 1)) (hj : j ∉ Idx.img n s) :
    Idx.img n (Twist.altInsert s j hj)
      = insert j (Idx.img n s) :=
  Twist.img_altOfFinset _ _

p2m_open_scoped "ProjSpaceCech.Twist" in

def Twist.insPos {i : ℕ} (s : Idx n i) (j : Fin (n + 1))
    (hj : j ∉ Idx.img n s) : Fin (i + 2) :=
  Twist.altPos (Twist.altInsert s j hj) j
    (by rw [Twist.img_altInsert]; exact Finset.mem_insert_self j _)

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.altInsert_val_insPos {i : ℕ} (s : Idx n i)
    (j : Fin (n + 1)) (hj : j ∉ Idx.img n s) :
    (Twist.altInsert s j hj).1 (Twist.insPos s j hj) = j :=
  Twist.idx_val_altPos _ j _

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.face_altInsert_insPos {i : ℕ} (s : Idx n i)
    (j : Fin (n + 1)) (hj : j ∉ Idx.img n s) :
    Idx.face n (Twist.altInsert s j hj)
      (Twist.insPos s j hj) = s := by
  apply Twist.idx_eq_of_img
  rw [Twist.img_face, Twist.altInsert_val_insPos,
    Twist.img_altInsert, Finset.erase_insert hj]

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.img_face_altInsert_ne {i : ℕ} (s : Idx n i)
    (j : Fin (n + 1)) (hj : j ∉ Idx.img n s)
    (k : Fin (i + 2)) (hk : k ≠ Twist.insPos s j hj) :
    ∃ (m : Fin (n + 1)), m ∈ Idx.img n s ∧ m ≠ j ∧
      Idx.img n (Idx.face n (Twist.altInsert s j hj) k)
        = insert j ((Idx.img n s).erase m) := by
  set m := (Twist.altInsert s j hj).1 k with hm_def
  have hmne : m ≠ j := by
    intro heq
    apply hk
    have : (Twist.altInsert s j hj).1 k
        = (Twist.altInsert s j hj).1 (Twist.insPos s j hj) := by
      rw [Twist.altInsert_val_insPos]; exact heq
    exact (Twist.altInsert s j hj).2.injective this
  have hmem : m ∈ Idx.img n s := by
    have : m ∈ Idx.img n (Twist.altInsert s j hj) :=
      Finset.mem_image_of_mem _ (Finset.mem_univ k)
    rw [Twist.img_altInsert] at this
    exact (Finset.mem_insert.mp this).resolve_left hmne
  refine ⟨m, hmem, hmne, ?_⟩
  rw [Twist.img_face, Twist.img_altInsert,
    Finset.erase_insert_of_ne hmne.symm]

variable (R : Type u) [CommRing R] (d : ℤ)

p2m_open_scoped "ProjSpaceCech.Twist" in

def Twist.coeff {i : ℕ} (f : Twist.cochain R n d i)
    (s : Idx n i) (a : Twist.MonExp n) : R :=
  if h : (∑ j, a j = d ∧ Twist.negSupp n a ⊆ Idx.img n s)
    then f s ⟨a, h⟩ else 0

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.coeff_eq {i : ℕ} (f : Twist.cochain R n d i)
    (s : Idx n i) (a : Twist.Mon n d (Idx.img n s)) :
    Twist.coeff R d f s a.1 = f s a := by
  rcases a with ⟨a, ha⟩
  rw [Twist.coeff, dif_pos ha]

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.coeff_of_not {i : ℕ} (f : Twist.cochain R n d i)
    (s : Idx n i) (a : Twist.MonExp n)
    (h : ¬ Twist.negSupp n a ⊆ Idx.img n s) :
    Twist.coeff R d f s a = 0 := by
  rw [Twist.coeff, dif_neg (fun h' => h h'.2)]

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.coeff_add {i : ℕ} (f g : Twist.cochain R n d i)
    (s : Idx n i) (a : Twist.MonExp n) :
    Twist.coeff R d (f + g) s a
      = Twist.coeff R d f s a + Twist.coeff R d g s a := by
  unfold Twist.coeff; split_ifs <;> simp [Pi.add_apply, Finsupp.add_apply]

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.coeff_smul {i : ℕ} (r : R) (f : Twist.cochain R n d i)
    (s : Idx n i) (a : Twist.MonExp n) :
    Twist.coeff R d (r • f) s a = r • Twist.coeff R d f s a := by
  unfold Twist.coeff; split_ifs <;> simp [Pi.smul_apply, Finsupp.smul_apply]

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.ext_coeff {i : ℕ} {f g : Twist.cochain R n d i}
    (h : ∀ s a, Twist.coeff R d f s a = Twist.coeff R d g s a) :
    f = g := by
  funext s; ext a
  have := h s a.1
  rwa [Twist.coeff_eq, Twist.coeff_eq] at this

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.coeff_d {i : ℕ} (f : Twist.cochain R n d i)
    (s : Idx n (i + 1)) (a : Twist.MonExp n) :
    Twist.coeff R d (Twist.d R n d i f) s a
      = ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
          Twist.coeff R d f (Idx.face n s j) a := by
  by_cases hok : (∑ j, a j = d ∧ Twist.negSupp n a ⊆ Idx.img n s)
  · rw [Twist.coeff, dif_pos hok, Twist.d_apply, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.smul_apply, Twist.faceRes, Finsupp.lmapDomain_apply]
    by_cases hface : Twist.negSupp n a ⊆ Idx.img n (Idx.face n s j)
    · rw [Twist.coeff, dif_pos ⟨hok.1, hface⟩]
      congr 1
      have key : (⟨a, hok⟩ : Twist.Mon n d (Idx.img n s))
          = Twist.Mon.incl n d (Idx.img_face_subset n s j)
              ⟨a, hok.1, hface⟩ := rfl
      rw [key, Finsupp.mapDomain_apply (Twist.Mon.incl_injective n d _)]
    · rw [Twist.coeff_of_not _ _ _ _ _ hface, smul_zero,
        Finsupp.mapDomain_notin_range, smul_zero]
      rintro ⟨⟨b, hb1, hb2⟩, hb⟩
      apply hface
      have : a = b := congrArg Subtype.val hb.symm
      exact this ▸ hb2
  · rw [Twist.coeff, dif_neg hok]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    rw [Twist.coeff, dif_neg, smul_zero]
    exact fun h' => hok ⟨h'.1, h'.2.trans (Idx.img_face_subset n s j)⟩

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.coeff_piSingle {i : ℕ} (s₀ : Idx n i)
    (b₀ : Twist.Mon n d (Idx.img n s₀)) (r : R)
    (s : Idx n i) (a : Twist.MonExp n) :
    Twist.coeff R d (Pi.single s₀ (Finsupp.single b₀ r)) s a
      = if s = s₀ ∧ a = b₀.1 then r else 0 := by
  by_cases hsa : s = s₀ ∧ a = b₀.1
  · obtain ⟨rfl, rfl⟩ := hsa
    rw [if_pos ⟨rfl, rfl⟩, Twist.coeff_eq, Pi.single_eq_same, Finsupp.single_eq_same]
  · rw [if_neg hsa, Twist.coeff]
    split_ifs with hok
    · by_cases hs : s = s₀
      · subst hs
        rw [Pi.single_eq_same, Finsupp.single_apply, if_neg]
        intro heq
        exact hsa ⟨rfl, (Subtype.ext_iff.mp heq : b₀.1 = a).symm⟩
      · rw [Pi.single_eq_of_ne hs, Finsupp.zero_apply]
    · rfl

p2m_open_scoped "ProjSpaceCech.Twist" in

def Twist.posMin (a : Twist.MonExp n)
    (ha : Twist.negSupp n a ≠ univ) : Fin (n + 1) :=
  (univ \ Twist.negSupp n a).min'
    (by rwa [Finset.nonempty_iff_ne_empty, Ne, Finset.sdiff_eq_empty_iff_subset,
      Finset.univ_subset_iff])

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.posMin_notMem_negSupp (a : Twist.MonExp n)
    (ha : Twist.negSupp n a ≠ univ) :
    Twist.posMin a ha ∉ Twist.negSupp n a := by
  have := Finset.min'_mem _
    (show (univ \ Twist.negSupp n a).Nonempty from
      by rwa [Finset.nonempty_iff_ne_empty, Ne, Finset.sdiff_eq_empty_iff_subset,
        Finset.univ_subset_iff])
  exact (Finset.mem_sdiff.mp this).2

end Homotopy

section Rank

variable {n : ℕ}

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.altPos_eq_card {i : ℕ} (s : Idx n i)
    (j : Fin (n + 1)) (hj : j ∈ Idx.img n s) :
    (Twist.altPos s j hj : ℕ) = #((Idx.img n s).filter (· < j)) := by
  set p := Twist.altPos s j hj
  have hval : s.1 p = j := Twist.idx_val_altPos s j hj
  have key : (Idx.img n s).filter (· < j) = (Finset.Iio p).image s.1 := by
    ext x
    simp only [Idx.img, mem_filter, mem_image, mem_univ, true_and, mem_Iio]
    constructor
    · rintro ⟨⟨k, rfl⟩, hlt⟩; exact ⟨k, s.2.lt_iff_lt.mp (hval ▸ hlt), rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, rfl⟩, hval ▸ s.2 hk⟩
  rw [key, Finset.card_image_of_injective _ s.2.injective, Fin.card_Iio]

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.insPos_eq_card {i : ℕ} (s : Idx n i)
    (j : Fin (n + 1)) (hj : j ∉ Idx.img n s) :
    (Twist.insPos s j hj : ℕ) = #((Idx.img n s).filter (· < j)) := by
  rw [Twist.insPos, Twist.altPos_eq_card, Twist.img_altInsert,
    Finset.filter_insert, if_neg (lt_irrefl j)]

end Rank

section Hj

variable {n : ℕ} (R : Type u) [CommRing R] (d : ℤ)

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.img_subset_altInsert {i : ℕ} (s : Idx n i)
    (j₁ : Fin (n + 1)) (hj : j₁ ∉ Idx.img n s) :
    Idx.img n s ⊆ Idx.img n (Twist.altInsert s j₁ hj) := by
  rw [Twist.img_altInsert]; exact Finset.subset_insert _ _

p2m_open_scoped "ProjSpaceCech.Twist" in

def Twist.hj (j₁ : Fin (n + 1)) (i : ℕ) :
    Twist.cochain R n d (i + 1) →ₗ[R] Twist.cochain R n d i :=
  LinearMap.pi fun s =>
    if hj : j₁ ∉ Idx.img n s then
      ((-1 : ℤ) ^ (Twist.insPos s j₁ hj : ℕ)) •
        ((Finsupp.lcomapDomain
            (Twist.Mon.incl n d (Twist.img_subset_altInsert s j₁ hj))
            (Twist.Mon.incl_injective n d _)).comp
          (LinearMap.proj (Twist.altInsert s j₁ hj)))
    else 0

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.hj_apply_of_mem (j₁ : Fin (n + 1)) {i : ℕ}
    (f : Twist.cochain R n d (i + 1)) (s : Idx n i)
    (hmem : j₁ ∈ Idx.img n s) :
    Twist.hj R d j₁ i f s = 0 := by
  simp only [Twist.hj, LinearMap.pi_apply, dif_neg (not_not.mpr hmem),
    LinearMap.zero_apply]

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.coeff_hj_of_mem (j₁ : Fin (n + 1)) {i : ℕ}
    (f : Twist.cochain R n d (i + 1)) (s : Idx n i)
    (a : Twist.MonExp n) (hmem : j₁ ∈ Idx.img n s) :
    Twist.coeff R d (Twist.hj R d j₁ i f) s a = 0 := by
  rw [Twist.coeff]; split_ifs with h
  · rw [Twist.hj_apply_of_mem R d j₁ f s hmem, Finsupp.zero_apply]
  · rfl

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.coeff_hj (j₁ : Fin (n + 1)) {i : ℕ}
    (f : Twist.cochain R n d (i + 1)) (s : Idx n i)
    (a : Twist.MonExp n) (hjs : j₁ ∉ Idx.img n s)
    (ha : Twist.negSupp n a ⊆ Idx.img n s) :
    Twist.coeff R d (Twist.hj R d j₁ i f) s a
      = ((-1 : ℤ) ^ (Twist.insPos s j₁ hjs : ℕ)) •
          Twist.coeff R d f (Twist.altInsert s j₁ hjs) a := by
  by_cases hsum : ∑ j, a j = d
  · have hok : ∑ j, a j = d ∧ Twist.negSupp n a ⊆ Idx.img n s := ⟨hsum, ha⟩
    have hok' : ∑ j, a j = d ∧ Twist.negSupp n a
        ⊆ Idx.img n (Twist.altInsert s j₁ hjs) :=
      ⟨hsum, ha.trans (Twist.img_subset_altInsert s j₁ hjs)⟩
    rw [Twist.coeff, dif_pos hok, Twist.hj, LinearMap.pi_apply, dif_pos hjs,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, Finsupp.smul_apply,
      Twist.coeff, dif_pos hok']
    rfl
  · rw [Twist.coeff, dif_neg (fun h => hsum h.1), Twist.coeff,
      dif_neg (fun h => hsum h.1), smul_zero]

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.coeff_zero {i : ℕ} (s : Idx n i)
    (a : Twist.MonExp n) :
    Twist.coeff R d (0 : Twist.cochain R n d i) s a = 0 := by
  rw [Twist.coeff]; split_ifs <;> simp [Finsupp.zero_apply]

end Hj

section DhHd

variable {n : ℕ} (R : Type u) [CommRing R] (d : ℤ)

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.dh_hd_coeff (j₁ : Fin (n + 1)) (i : ℕ)
    (s : Idx n (i + 1)) (a : Twist.MonExp n)
    (hsub : Twist.negSupp n a ⊆ Idx.img n s)
    (haj : j₁ ∉ Twist.negSupp n a)
    (f : Twist.cochain R n d (i + 1)) :
    Twist.coeff R d
        (Twist.d R n d i (Twist.hj R d j₁ i f)) s a
      + Twist.coeff R d
          (Twist.hj R d j₁ (i + 1) (Twist.d R n d (i + 1) f)) s a
      = Twist.coeff R d f s a := by
  rw [Twist.coeff_d]
  by_cases hmem : j₁ ∈ Idx.img n s
  ·
    set p := Twist.altPos s j₁ hmem with hp_def
    rw [Twist.coeff_hj_of_mem R d j₁ _ s a hmem, add_zero,
      Finset.sum_eq_single p (fun j _ hjp => ?_) (fun h => absurd (Finset.mem_univ p) h)]
    · have hjp : s.1 p = j₁ := Twist.idx_val_altPos s j₁ hmem
      have hfjp : j₁ ∉ Idx.img n (Idx.face n s p) := by
        rw [Twist.img_face, hjp]; exact Finset.notMem_erase _ _
      have hsub' : Twist.negSupp n a
          ⊆ Idx.img n (Idx.face n s p) := by
        rw [Twist.img_face, hjp]; exact Finset.subset_erase.mpr ⟨hsub, haj⟩
      rw [Twist.coeff_hj R d j₁ f _ a hfjp hsub', smul_smul, ← pow_add]
      have hins : Twist.altInsert (Idx.face n s p) j₁ hfjp = s := by
        apply Twist.idx_eq_of_img
        rw [Twist.img_altInsert, Twist.img_face, hjp,
          Finset.insert_erase hmem]
      have hsign : (Twist.insPos (Idx.face n s p) j₁ hfjp : ℕ) = p := by
        rw [Twist.insPos_eq_card, Twist.img_face, hjp,
          Finset.filter_erase, Finset.erase_eq_of_notMem
            (by simp only [mem_filter, lt_irrefl, and_false, not_false_iff]),
          ← Twist.altPos_eq_card s j₁ hmem]
      rw [hsign, ← two_mul, (even_two_mul (p : ℕ)).neg_one_pow, one_smul]
      exact congrArg (fun t => Twist.coeff R d f t a) hins
    ·
      have hne : s.1 j ≠ j₁ := fun heq => hjp
        (s.2.injective (heq.trans (Twist.idx_val_altPos s j₁ hmem).symm))
      rw [Twist.coeff_hj_of_mem R d j₁ f _ a
        (by rw [Twist.img_face]; exact Finset.mem_erase.mpr ⟨Ne.symm hne, hmem⟩),
        smul_zero]
  ·
    set q := Twist.insPos s j₁ hmem with hq_def
    rw [Twist.coeff_hj R d j₁ _ s a hmem hsub, Twist.coeff_d,
      Finset.smul_sum,
      show (Finset.univ : Finset (Fin (i + 3))) = insert q (Finset.univ.erase q) from
        (Finset.insert_erase (Finset.mem_univ q)).symm,
      Finset.sum_insert (Finset.notMem_erase q _),
      Twist.face_altInsert_insPos s j₁ hmem,
      smul_smul, ← pow_add, ← two_mul,
      (even_two_mul (q : ℕ)).neg_one_pow, one_smul, add_left_comm, add_eq_left,
      add_eq_zero_iff_eq_neg, ← Finset.sum_neg_distrib]

    have hmem_j : ∀ j : Fin (i + 2),
        s.1 j ∈ Idx.img n (Twist.altInsert s j₁ hmem) := fun j => by
      rw [Twist.img_altInsert]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    have hmem_k : ∀ k ∈ Finset.univ.erase q,
        (Twist.altInsert s j₁ hmem).1 k ∈ Idx.img n s := fun k hk => by
      have hkq : k ≠ q := (Finset.mem_erase.mp hk).1
      have hne_j₁ : (Twist.altInsert s j₁ hmem).1 k ≠ j₁ := fun heq => hkq
        ((Twist.altInsert s j₁ hmem).2.injective
          (heq.trans (Twist.altInsert_val_insPos s j₁ hmem).symm))
      have : (Twist.altInsert s j₁ hmem).1 k
          ∈ Idx.img n (Twist.altInsert s j₁ hmem) :=
        Finset.mem_image_of_mem _ (Finset.mem_univ k)
      rw [Twist.img_altInsert] at this
      exact (Finset.mem_insert.mp this).resolve_left hne_j₁
    refine Finset.sum_bij'
      (fun j _ => Twist.altPos (Twist.altInsert s j₁ hmem) (s.1 j) (hmem_j j))
      (fun k hk => Twist.altPos s ((Twist.altInsert s j₁ hmem).1 k)
        (hmem_k k hk))
      (fun j _ => Finset.mem_erase.mpr ⟨fun heq => hmem (by
        have heq' : Twist.altPos (Twist.altInsert s j₁ hmem) (s.1 j)
          (hmem_j j) = q := heq
        have hval := Twist.idx_val_altPos (Twist.altInsert s j₁ hmem)
          (s.1 j) (hmem_j j)
        rw [heq', hq_def, Twist.altInsert_val_insPos] at hval
        exact hval ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j)),
        Finset.mem_univ _⟩)
      (fun k hk => Finset.mem_univ _)
      (fun j _ => s.2.injective
        ((Twist.idx_val_altPos s _ _).trans
          (Twist.idx_val_altPos (Twist.altInsert s j₁ hmem) _ _)))
      (fun k hk => (Twist.altInsert s j₁ hmem).2.injective
        ((Twist.idx_val_altPos (Twist.altInsert s j₁ hmem) _ _).trans
          (Twist.idx_val_altPos s _ _)))
      (fun j _ => ?_)

    set m := s.1 j with hm_def
    have hms : m ∈ Idx.img n s := Finset.mem_image_of_mem _ (Finset.mem_univ j)
    have hmj₁ : m ≠ j₁ := fun h => hmem (h ▸ hms)
    have hjface : j₁ ∉ Idx.img n (Idx.face n s j) := fun h =>
      hmem ((Idx.img_face_subset n s j) h)
    set k := Twist.altPos (Twist.altInsert s j₁ hmem) m (hmem_j j)
    have hk_val : (Twist.altInsert s j₁ hmem).1 k = m :=
      Twist.idx_val_altPos _ m _
    have heq_tgt : Twist.altInsert (Idx.face n s j) j₁ hjface
        = Idx.face n (Twist.altInsert s j₁ hmem) k := by
      apply Twist.idx_eq_of_img
      rw [Twist.img_altInsert, Twist.img_face,
        Twist.img_face, Twist.img_altInsert, hk_val, ← hm_def,
        Finset.erase_insert_of_ne hmj₁.symm]
    by_cases hmneg : m ∈ Twist.negSupp n a
    ·
      have hnot : ¬ Twist.negSupp n a
          ⊆ Idx.img n (Idx.face n s j) := fun h => by
        rw [Twist.img_face, ← hm_def] at h
        exact (Finset.notMem_erase m _) (h hmneg)
      have hnot' : ¬ Twist.negSupp n a
          ⊆ Idx.img n (Idx.face n (Twist.altInsert s j₁ hmem)
            k) := fun h => by
        rw [← heq_tgt, Twist.img_altInsert] at h
        exact hnot (fun x hx => (Finset.mem_insert.mp (h hx)).resolve_left
          (fun hx' => haj (hx' ▸ hx)))
      rw [Twist.coeff_of_not _ _ _ _ _ hnot, smul_zero,
        Twist.coeff_of_not _ _ _ _ _ hnot', smul_zero, smul_zero, neg_zero]
    ·
      have hsub' : Twist.negSupp n a
          ⊆ Idx.img n (Idx.face n s j) := by
        rw [Twist.img_face, ← hm_def]; exact Finset.subset_erase.mpr ⟨hsub, hmneg⟩
      rw [Twist.coeff_hj R d j₁ f _ a hjface hsub', smul_smul, smul_smul, heq_tgt,
        ← neg_smul, ← pow_add, ← pow_add]
      congr 1

      set P := #((Idx.img n s).filter (· < j₁)) with hP_def
      set Q := #((Idx.img n s).filter (· < m)) with hQ_def
      have hjQ : (j : ℕ) = Q := by
        have h := Twist.altPos_eq_card s (s.1 j)
          (Finset.mem_image_of_mem _ (Finset.mem_univ j))
        rw [Twist.altPos_val] at h; rw [hQ_def, hm_def]; exact h
      have hqP : (q : ℕ) = P := hq_def ▸ Twist.insPos_eq_card s j₁ hmem
      have hkval : (k : ℕ) = Q + (if j₁ < m then 1 else 0) := by
        rw [Twist.altPos_eq_card, Twist.img_altInsert,
          Finset.filter_insert, hQ_def]
        split_ifs with h
        · rw [Finset.card_insert_of_notMem (by simp [mem_filter, hmem])]
        · rfl
      have hinsval :
          (Twist.insPos (Idx.face n s j) j₁ hjface : ℕ)
            = P - (if m < j₁ then 1 else 0) := by
        rw [Twist.insPos_eq_card, Twist.img_face, ← hm_def,
          Finset.filter_erase, hP_def]
        split_ifs with h
        · rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hms, h⟩)]
        · rw [Finset.erase_eq_of_notMem (by simp [mem_filter, h])]; omega
      have hPpos : (if m < j₁ then 1 else 0) ≤ P := by
        split_ifs with h
        · exact Nat.one_le_iff_ne_zero.mpr
            (Finset.card_ne_zero.mpr ⟨m, Finset.mem_filter.mpr ⟨hms, h⟩⟩)
        · exact Nat.zero_le _
      have htri : (if j₁ < m then 1 else 0) + (if m < j₁ then (1:ℕ) else 0) = 1 := by
        rcases lt_trichotomy j₁ m with h | h | h
        · simp [h, not_lt.mpr h.le]
        · exact absurd h hmj₁.symm
        · simp [h, not_lt.mpr h.le]
      rw [hjQ, hqP, hkval, hinsval,
        show P + (Q + (if j₁ < m then 1 else 0))
          = Q + (P - (if m < j₁ then 1 else 0)) + 1 from by omega, pow_succ]
      ring

end DhHd

section Homot

variable {n : ℕ} (R : Type u) [CommRing R] (d : ℤ)

p2m_open_scoped "ProjSpaceCech.Twist" in

def Twist.coeffL {i : ℕ} (s : Idx n i)
    (a : Twist.MonExp n) : Twist.cochain R n d i →ₗ[R] R where
  toFun f := Twist.coeff R d f s a
  map_add' f g := Twist.coeff_add R d f g s a
  map_smul' r f := Twist.coeff_smul R d r f s a

p2m_open_scoped "ProjSpaceCech.Twist" in

def Twist.homot (i : ℕ) :
    Twist.cochain R n d (i + 1) →ₗ[R] Twist.cochain R n d i :=
  ∑ s' : Idx n (i + 1),
    (Finsupp.lsum ℕ fun b =>
      if hb : Twist.negSupp n b.1 ≠ Finset.univ then
        (Twist.hj R d (Twist.posMin b.1 hb) i).comp
          ((LinearMap.single R _ s').comp (Finsupp.lsingle b))
      else 0).comp
    (LinearMap.proj s')

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.homot_basis {i : ℕ} (s₀ : Idx n (i + 1))
    (b₀ : Twist.Mon n d (Idx.img n s₀)) (r : R) :
    Twist.homot R d i (Pi.single s₀ (Finsupp.single b₀ r))
      = if hb : Twist.negSupp n b₀.1 ≠ Finset.univ then
          Twist.hj R d (Twist.posMin b₀.1 hb) i
            (Pi.single s₀ (Finsupp.single b₀ r)) else 0 := by
  unfold Twist.homot
  rw [LinearMap.sum_apply,
    Finset.sum_eq_single s₀ (fun s' _ hne => by
      rw [LinearMap.comp_apply, LinearMap.proj_apply, Pi.single_eq_of_ne hne, map_zero])
      (fun h => absurd (Finset.mem_univ s₀) h)]
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, Pi.single_eq_same, Finsupp.lsum_single]
  split_ifs with hb
  · simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.single_apply]
  · rfl

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.coeff_homot {i : ℕ} (t : Idx n i)
    (a : Twist.MonExp n) (hsub : Twist.negSupp n a ⊆ Idx.img n t)
    (hne : Twist.negSupp n a ≠ Finset.univ)
    (f : Twist.cochain R n d (i + 1)) :
    Twist.coeff R d (Twist.homot R d i f) t a
      = Twist.coeff R d
          (Twist.hj R d (Twist.posMin a hne) i f) t a := by
  set j₁ := Twist.posMin a hne

  have hkey : (Twist.coeffL R d t a).comp (Twist.homot R d i)
      = (Twist.coeffL R d t a).comp (Twist.hj R d j₁ i) := by
    refine LinearMap.pi_ext' fun s₀ => Finsupp.lhom_ext fun b₀ r => ?_
    simp only [LinearMap.comp_apply, LinearMap.single_apply]
    change Twist.coeff R d (Twist.homot R d i _) t a
      = Twist.coeff R d (Twist.hj R d j₁ i _) t a
    rw [Twist.homot_basis]

    have hvanish : ∀ j', a ≠ b₀.1 →
        Twist.coeff R d (Twist.hj R d j' i
          (Pi.single s₀ (Finsupp.single b₀ r))) t a = 0 := by
      intro j' hab
      by_cases hj't : j' ∈ Idx.img n t
      · exact Twist.coeff_hj_of_mem R d j' _ t a hj't
      · rw [Twist.coeff_hj R d j' _ t a hj't hsub, Twist.coeff_piSingle,
          if_neg (fun h => hab h.2), smul_zero]
    by_cases hab : a = b₀.1
    · subst hab; rw [dif_pos hne]
    · split_ifs with hb
      · rw [hvanish _ hab, hvanish _ hab]
      · rw [Twist.coeff_zero, hvanish _ hab]
  exact congrFun (congrArg DFunLike.coe hkey) f

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.subsingleton_cohomology_succ_of_le {i : ℕ} (hi : i + 2 ≤ n) :
    Subsingleton (Twist.H R n d (i + 1)) := by
  dsimp only [Twist.H]
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
  rintro ⟨f, hf⟩
  refine Submodule.mem_comap.mpr ⟨Twist.homot R d i f, Twist.ext_coeff R d ?_⟩
  intro s a
  by_cases hok : ∑ j, a j = d ∧ Twist.negSupp n a ⊆ Idx.img n s
  · have hne : Twist.negSupp n a ≠ Finset.univ := fun h => by
      have := Finset.card_le_card (h ▸ hok.2)
      rw [Idx.card_img, Finset.card_univ, Fintype.card_fin] at this; omega
    set j₁ := Twist.posMin a hne
    have haj : j₁ ∉ Twist.negSupp n a := Twist.posMin_notMem_negSupp a hne
    rw [Twist.coeff_d]
    have hstep : ∀ j : Fin (i + 2),
        Twist.coeff R d (Twist.homot R d i f) (Idx.face n s j) a
          = Twist.coeff R d (Twist.hj R d j₁ i f)
              (Idx.face n s j) a := fun j => by
      by_cases hface : Twist.negSupp n a
          ⊆ Idx.img n (Idx.face n s j)
      · exact Twist.coeff_homot R d _ a hface hne f
      · rw [Twist.coeff_of_not _ _ _ _ _ hface,
          Twist.coeff_of_not _ _ _ _ _ hface]
    simp_rw [hstep]
    rw [← Twist.coeff_d]
    have hdf : Twist.d R n d (i + 1) f = 0 := (LinearMap.mem_ker).mp hf
    have key := Twist.dh_hd_coeff R d j₁ i s a hok.2 haj f
    rwa [hdf, map_zero, Twist.coeff_zero, add_zero] at key
  · rw [Twist.coeff, dif_neg hok, Twist.coeff, dif_neg hok]

end Homot

section HZero

variable {n : ℕ} (R : Type u) [CommRing R] (d : ℤ)

p2m_open_scoped "ProjSpaceCech.Twist" in

def Twist.vtx (j : Fin (n + 1)) : Idx n 0 :=
  ⟨fun _ => j, fun a b h => absurd h (by omega)⟩

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.img_vtx (j : Fin (n + 1)) :
    Idx.img n (Twist.vtx j) = {j} := by
  rw [Idx.img, Twist.vtx]; ext x
  simp only [mem_image, mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨0, h.symm⟩⟩

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.eq_vtx (t : Idx n 0) :
    t = Twist.vtx (t.1 0) := by
  exact Subtype.ext (funext fun p => Fin.fin_one_eq_zero p ▸ rfl)

p2m_open_scoped "ProjSpaceCech.Twist" in
scoped instance Twist.mon_empty_finite :
    Finite (Twist.Mon n d ∅) := by
  by_cases hd : 0 ≤ d
  · refine Finite.of_injective
      (β := Fin (n + 1) → Fin (d.toNat + 1))
      (fun a j => ⟨(a.1 j).toNat, ?_⟩) ?_
    · have hnn : ∀ k, 0 ≤ a.1 k := fun k => not_lt.mp fun h =>
        (Finset.notMem_empty k) (a.2.2 ((Twist.mem_negSupp n).mpr h))
      have hle : a.1 j ≤ d := (Finset.single_le_sum (fun k _ => hnn k)
        (Finset.mem_univ j)).trans_eq a.2.1
      omega
    · intro a b hab
      refine Subtype.ext (funext fun j => ?_)
      have hnn_a : 0 ≤ a.1 j := not_lt.mp fun h =>
        (Finset.notMem_empty j) (a.2.2 ((Twist.mem_negSupp n).mpr h))
      have hnn_b : 0 ≤ b.1 j := not_lt.mp fun h =>
        (Finset.notMem_empty j) (b.2.2 ((Twist.mem_negSupp n).mpr h))
      have := congrFun hab j; simp only [Fin.mk.injEq] at this; omega
  · have : IsEmpty (Twist.Mon n d ∅) := ⟨fun a => hd
      ((Finset.sum_nonneg fun k _ => not_lt.mp fun h =>
        (Finset.notMem_empty k) (a.2.2 ((Twist.mem_negSupp n).mpr h))).trans_eq a.2.1)⟩
    infer_instance

p2m_reactivate "P2MW.S_ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist"
p2m_open_scoped "ProjSpaceCech.Twist" in

def Twist.constSec :
    (Twist.Mon n d ∅ →₀ R) →ₗ[R] Twist.cochain R n d 0 :=
  LinearMap.pi fun s =>
    Finsupp.lmapDomain R R (Twist.Mon.incl n d (Finset.empty_subset _))

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.coeff_constSec (g : Twist.Mon n d ∅ →₀ R)
    (t : Idx n 0) (a : Twist.MonExp n) :
    Twist.coeff R d (Twist.constSec R d g) t a
      = if h : (∑ j, a j = d ∧ Twist.negSupp n a = ∅) then g ⟨a, h.1, h.2.le⟩
        else 0 := by
  rw [Twist.coeff, Twist.constSec, LinearMap.pi_apply, Finsupp.lmapDomain_apply]
  split_ifs with h1 h2 h3
  · have key : (⟨a, h1⟩ : Twist.Mon n d (Idx.img n t))
        = Twist.Mon.incl n d (Finset.empty_subset _) ⟨a, h2.1, h2.2.le⟩ := rfl
    rw [key, Finsupp.mapDomain_apply (Twist.Mon.incl_injective n d _)]
  · rw [Finsupp.mapDomain_notin_range]
    rintro ⟨b, hb⟩
    refine h2 ⟨h1.1, ?_⟩
    have : b.1 = a := congrArg Subtype.val hb
    exact this ▸ Finset.subset_empty.mp b.2.2
  · exact absurd ⟨h3.1, h3.2.le.trans (Finset.empty_subset _)⟩ h1
  · rfl

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.constSec_mem_ker (g : Twist.Mon n d ∅ →₀ R) :
    Twist.constSec R d g ∈ LinearMap.ker (Twist.d R n d 0) := by
  rw [LinearMap.mem_ker]
  refine Twist.ext_coeff R d fun s a => ?_
  rw [Twist.coeff_d, Fin.sum_univ_two, Twist.coeff_constSec,
    Twist.coeff_constSec, Twist.coeff_zero]
  split_ifs <;> simp

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.ker_edge {f : Twist.cochain R n d 0}
    (hf : f ∈ LinearMap.ker (Twist.d R n d 0))
    (j k : Fin (n + 1)) (a : Twist.MonExp n) :
    Twist.coeff R d f (Twist.vtx j) a
      = Twist.coeff R d f (Twist.vtx k) a := by
  have aux : ∀ x y : Fin (n + 1), x < y →
      Twist.coeff R d f (Twist.vtx x) a
        = Twist.coeff R d f (Twist.vtx y) a := by
    intro x y hxy
    set s : Idx n 1 := ⟨![x, y], by
      intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [hxy]⟩
    have hf0 : (Idx.face n s 0) = Twist.vtx y :=
      Subtype.ext (funext fun p => Fin.fin_one_eq_zero p ▸ rfl)
    have hf1 : (Idx.face n s 1) = Twist.vtx x :=
      Subtype.ext (funext fun p => Fin.fin_one_eq_zero p ▸ rfl)
    have hd0 : Twist.coeff R d (Twist.d R n d 0 f) s a = 0 := by
      rw [(LinearMap.mem_ker).mp hf, Twist.coeff_zero]
    rw [Twist.coeff_d, Fin.sum_univ_two] at hd0
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul,
      hf0, hf1] at hd0
    exact (add_neg_eq_zero.mp hd0).symm
  rcases lt_trichotomy j k with h | rfl | h
  · exact aux j k h
  · rfl
  · exact (aux k j h).symm

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.H_zero_finite (hn : 1 ≤ n) :
    Module.Finite R (Twist.H R n d 0) := by
  have : Module.Finite R (Twist.Mon n d ∅ →₀ R) := Module.Finite.finsupp
  refine Module.Finite.of_surjective
    (show (Twist.Mon n d ∅ →₀ R) →ₗ[R] Twist.H R n d 0 from
      (Twist.constSec R d).codRestrict
        (LinearMap.ker (Twist.d R n d 0))
        (Twist.constSec_mem_ker R d))
    ?_
  intro x
  obtain ⟨f, hf⟩ := x
  refine ⟨Finsupp.comapDomain (Twist.Mon.incl n d (Finset.empty_subset _))
    (f (Twist.vtx 0))
    (Set.injOn_of_injective (Twist.Mon.incl_injective n d _)),
    Subtype.ext (Twist.ext_coeff R d fun t a => ?_)⟩
  change Twist.coeff R d (Twist.constSec R d _) t a
    = Twist.coeff R d f t a
  rw [Twist.coeff_constSec]
  split_ifs with hok
  · rw [Finsupp.comapDomain_apply,
      show Twist.Mon.incl n d (Finset.empty_subset _) ⟨a, hok.1, hok.2.le⟩
        = (⟨a, hok.1, hok.2.le.trans (Finset.empty_subset _)⟩ :
          Twist.Mon n d (Idx.img n (Twist.vtx 0))) from rfl,
      ← Twist.coeff_eq R d f (Twist.vtx 0),
      Twist.eq_vtx t, Twist.ker_edge R d hf]
  · by_cases hokt : ∑ j, a j = d ∧ Twist.negSupp n a ⊆ Idx.img n t
    ·
      have hns : Twist.negSupp n a ⊆ {t.1 0} := by
        rw [← Twist.img_vtx (t.1 0), ← Twist.eq_vtx t]; exact hokt.2
      have hne : Twist.negSupp n a ≠ ∅ := fun h => hok ⟨hokt.1, h⟩
      obtain ⟨k, hk⟩ : ∃ k : Fin (n + 1), k ≠ t.1 0 :=
        Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) (t.1 0)
      rw [Twist.eq_vtx t, Twist.ker_edge R d hf (t.1 0) k,
        Twist.coeff_of_not]
      rw [Twist.img_vtx]
      exact fun h => hk ((Finset.mem_singleton.mp
        (h (Finset.nonempty_iff_ne_empty.mpr hne).choose_spec)).symm.trans
        (Finset.mem_singleton.mp (hns (Finset.nonempty_iff_ne_empty.mpr hne).choose_spec)))
    · rw [Twist.coeff, dif_neg hokt]

end HZero
p2m_reactivate "P2MW.S_ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist"

section HN

variable {m : ℕ} (R : Type u) [CommRing R] (d : ℤ)

p2m_open_scoped "ProjSpaceCech.Twist" in

def Twist.sfull : Idx (m + 1) (m + 1) := ⟨id, strictMono_id⟩

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.img_sfull :
    Idx.img (m + 1) (Twist.sfull (m := m)) = Finset.univ := by
  simp [Idx.img, Twist.sfull, Finset.image_id]

p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.eq_sfull (s : Idx (m + 1) (m + 1)) :
    s = Twist.sfull := by
  apply Twist.idx_eq_of_img
  rw [Twist.img_sfull, ← Finset.card_eq_iff_eq_univ, Idx.card_img,
    Fintype.card_fin]

p2m_open_scoped "ProjSpaceCech.Twist" in

scoped instance Twist.mon_allNeg_finite :
    Finite {b : Twist.Mon (m + 1) d
      (Idx.img (m + 1) (Twist.sfull (m := m))) //
      Twist.negSupp (m + 1) b.1 = Finset.univ} := by
  have hall : ∀ (a : {b : Twist.Mon (m + 1) d
      (Idx.img (m + 1) (Twist.sfull (m := m))) //
      Twist.negSupp (m + 1) b.1 = Finset.univ}) k, a.1.1 k < 0 := fun a k =>
    (Twist.mem_negSupp (m + 1)).mp (by rw [a.2]; exact Finset.mem_univ k)
  refine Finite.of_injective (β := Fin (m + 2) → Fin ((-d).toNat + 1))
    (fun a j => ⟨(-1 - a.1.1 j).toNat, by
      have hbound : ∑ k, (-1 - a.1.1 k) = -(m + 2 : ℤ) - d := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          a.1.2.1]; ring
      have hle : -1 - a.1.1 j ≤ ∑ k, (-1 - a.1.1 k) := by
        have := Finset.single_le_sum (s := (Finset.univ : Finset (Fin (m + 2))))
          (f := fun k => (-1 : ℤ) - a.1.1 k)
          (fun k _ => by have := hall a k; omega) (Finset.mem_univ j)
        simpa using this
      have := hall a j; omega⟩)
    (fun a b hab => Subtype.ext (Subtype.ext (funext fun j => by
      have ha := hall a j; have hb := hall b j
      have := congrFun hab j; simp only [Fin.mk.injEq] at this; omega)))

p2m_reactivate "P2MW.S_ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist"
p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.basis_mem_range
    (b : Twist.Mon (m + 1) d
      (Idx.img (m + 1) (Twist.sfull (m := m))))
    (hb : Twist.negSupp (m + 1) b.1 ≠ Finset.univ) (r : R) :
    Pi.single (Twist.sfull (m := m)) (Finsupp.single b r)
      ∈ LinearMap.range (Twist.d R (m + 1) d m) := by
  set j₁ := Twist.posMin b.1 hb
  have haj : j₁ ∉ Twist.negSupp (m + 1) b.1 := Twist.posMin_notMem_negSupp b.1 hb
  set e : Twist.cochain R (m + 1) d (m + 1) :=
    Pi.single Twist.sfull (Finsupp.single b r)
  refine ⟨Twist.hj R d j₁ m e, Twist.ext_coeff R d fun s a => ?_⟩
  rw [Twist.eq_sfull s]
  have hsub : Twist.negSupp (m + 1) a
      ⊆ Idx.img (m + 1) (Twist.sfull (m := m)) := by
    rw [Twist.img_sfull]; exact Finset.subset_univ _
  have hde : Twist.d R (m + 1) d (m + 1) e = 0 :=
    (Twist.cochain_subsingleton_of_lt R (m + 1) d (by omega)).elim _ 0
  by_cases hajneg : j₁ ∈ Twist.negSupp (m + 1) a
  ·
    have hab : a ≠ b.1 := fun h => haj (h ▸ hajneg)
    rw [Twist.coeff_d, Finset.sum_eq_zero, Twist.coeff_piSingle,
      if_neg (fun h => hab h.2)]
    intro j _
    by_cases hjf : j₁ ∈ Idx.img (m + 1)
        (Idx.face (m + 1) Twist.sfull j)
    · rw [Twist.coeff_hj_of_mem R d j₁ e _ a hjf, smul_zero]
    · rw [Twist.coeff_of_not _ _ _ _ _ (fun h => hjf (h hajneg)), smul_zero]
  · have key := Twist.dh_hd_coeff R d j₁ m Twist.sfull a hsub hajneg e
    rwa [hde, map_zero, Twist.coeff_zero, add_zero] at key

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.H_top_finite :
    Module.Finite R (Twist.H R (m + 1) d (m + 1)) := by
  set K := LinearMap.ker (Twist.d R (m + 1) d (m + 1))
  set Q := (LinearMap.range (Twist.d R (m + 1) d m)).comap K.subtype
  set S := {b : Twist.Mon (m + 1) d
    (Idx.img (m + 1) (Twist.sfull (m := m))) //
    Twist.negSupp (m + 1) b.1 = Finset.univ}
  have : Module.Finite R (S →₀ R) := Module.Finite.finsupp
  have hKtop : ∀ x, x ∈ K := fun x => LinearMap.mem_ker.mpr
    ((Twist.cochain_subsingleton_of_lt R (m + 1) d (by omega)).elim _ 0)
  refine Module.Finite.of_surjective
    (show (S →₀ R) →ₗ[R] Twist.H R (m + 1) d (m + 1) from
      Q.mkQ.comp ((Finsupp.lsum ℕ fun b : S =>
        (LinearMap.single R _ (Twist.sfull (m := m))).comp
          (Finsupp.lsingle b.1)).codRestrict K (fun g => hKtop _))) ?_
  intro x
  obtain ⟨⟨f, hf⟩, rfl⟩ := Q.mkQ_surjective x

  have hfeq : f = Pi.single (Twist.sfull (m := m)) (f Twist.sfull) := by
    funext s; rw [Twist.eq_sfull s, Pi.single_eq_same]
  set g := Finsupp.comapDomain (Subtype.val : S → _) (f Twist.sfull)
    (Set.injOn_of_injective Subtype.val_injective) with hg_def
  refine ⟨g, ?_⟩
  change Q.mkQ (LinearMap.codRestrict K _ _ g) = Q.mkQ ⟨f, hf⟩
  rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_comap, Submodule.subtype_apply, AddSubgroupClass.coe_sub,
    LinearMap.codRestrict_apply]

  set L : Twist.Sec R (m + 1) d (Idx.img (m + 1) Twist.sfull)
      →ₗ[R] Twist.cochain R (m + 1) d (m + 1) :=
    LinearMap.single R
      (fun s => Twist.Sec R (m + 1) d (Idx.img (m + 1) s))
      (Twist.sfull (m := m)) with hL_def
  have hstep : (Finsupp.lsum ℕ fun b : S => L.comp (Finsupp.lsingle b.1))
      = L.comp (Finsupp.lmapDomain R R (Subtype.val : S → _)) :=
    Finsupp.lhom_ext fun b r => by
      rw [Finsupp.lsum_single, LinearMap.comp_apply, LinearMap.comp_apply,
        Finsupp.lsingle_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [show (Finsupp.lsum ℕ fun b : S =>
      (LinearMap.single R _ (Twist.sfull (m := m))).comp (Finsupp.lsingle b.1)) g
      = (Finsupp.lsum ℕ fun b : S => L.comp (Finsupp.lsingle b.1)) g from rfl, hstep,
    LinearMap.comp_apply, Finsupp.lmapDomain_apply, ← neg_sub]

  refine neg_mem ?_
  have hdiff : (f : Twist.cochain R (m + 1) d (m + 1))
      - L (Finsupp.mapDomain Subtype.val g)
      = L ((f Twist.sfull).filter
          (fun b => Twist.negSupp (m + 1) b.1 ≠ Finset.univ)) := by
    conv_lhs => rw [hfeq]
    rw [hL_def, LinearMap.single_apply, LinearMap.single_apply, ← Pi.single_sub]
    congr 1
    refine Finsupp.ext fun b => ?_
    rw [Finsupp.sub_apply, Finsupp.filter_apply]
    by_cases hb : Twist.negSupp (m + 1) b.1 = Finset.univ
    · rw [if_neg (not_not.mpr hb), sub_eq_zero]
      have hkey : b = (Subtype.val : S → _) ⟨b, hb⟩ := rfl
      rw [hkey, Finsupp.mapDomain_apply Subtype.val_injective, hg_def,
        Finsupp.comapDomain_apply]
    · rw [if_pos hb, Finsupp.mapDomain_notin_range, sub_zero]
      rintro ⟨c, hc⟩; exact hb (hc ▸ c.2)
  rw [hdiff, show ((f Twist.sfull).filter
      (fun b => Twist.negSupp (m + 1) b.1 ≠ Finset.univ))
        = ((f Twist.sfull).filter
      (fun b => Twist.negSupp (m + 1) b.1 ≠ Finset.univ)).sum Finsupp.single from
    (Finsupp.sum_single _).symm,
    map_finsuppSum]
  refine Submodule.finsuppSum_mem _ _ _ _ fun b hbsup => ?_
  rw [hL_def, LinearMap.single_apply]
  have hb : Twist.negSupp (m + 1) b.1 ≠ Finset.univ := by
    by_contra h
    exact hbsup (Finsupp.filter_apply_neg _ _ (fun hne => hne h))
  exact Twist.basis_mem_range R d b hb _

end HN
p2m_reactivate "P2MW.S_ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist"

section Headline

variable (R : Type u) [CommRing R]

p2m_open_scoped "ProjSpaceCech.Twist" in
scoped instance Twist.mon_zero_finite (d : ℤ) (I : Finset (Fin 1)) :
    Finite (Twist.Mon 0 d I) :=
  Finite.of_injective (fun _ => (0 : Unit)) (fun a b _ => Subtype.ext
    (funext fun j => by
      have ha := a.2.1; have hb := b.2.1
      rw [Fin.sum_univ_one] at ha hb
      rw [Fin.fin_one_eq_zero j, ha, hb]))

p2m_reactivate "P2MW.S_ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist"
p2m_open_scoped "ProjSpaceCech.Twist" in
theorem Twist.finite_of_subsingleton (n : ℕ) (d : ℤ) (i : ℕ)
    (h : Subsingleton (Twist.H R n d i)) :
    Module.Finite R (Twist.H R n d i) :=
  ⟨⟨∅, by rw [Submodule.eq_top_iff']; exact fun x => h.elim x 0 ▸ Submodule.zero_mem _⟩⟩

p2m_open_scoped "ProjSpaceCech.Twist" in

theorem Twist.finite_cohomology (n : ℕ) (d : ℤ) (i : ℕ) :
    Module.Finite R (Twist.H R n d i) := by
  rcases n with _ | m
  ·
    rcases i with _ | j
    · have hsrc : Module.Finite R (Twist.cochain R 0 d 0) := by
        dsimp only [Twist.cochain]; infer_instance
      exact Module.Finite.of_surjective
        (show Twist.cochain R 0 d 0 →ₗ[R] Twist.H R 0 d 0 from
          LinearMap.id.codRestrict (LinearMap.ker (Twist.d R 0 d 0))
            (fun x => LinearMap.mem_ker.mpr
              ((Twist.cochain_subsingleton_of_lt R 0 d Nat.zero_lt_one).elim _ 0)))
        (fun ⟨x, hx⟩ => ⟨x, rfl⟩)
    · exact Twist.finite_of_subsingleton R 0 d (j + 1)
        (Twist.subsingleton_cohomology_of_lt R 0 d (Nat.succ_pos j))
  ·
    rcases i with _ | j
    · exact Twist.H_zero_finite R d (Nat.succ_pos m)
    rcases lt_trichotomy (j + 1) (m + 1) with hlt | heq | hgt
    · exact Twist.finite_of_subsingleton R (m + 1) d (j + 1)
        (Twist.subsingleton_cohomology_succ_of_le (n := m + 1) R d (i := j) (by omega))
    · obtain rfl : j = m := Nat.succ_injective heq
      exact Twist.H_top_finite R d
    · exact Twist.finite_of_subsingleton R (m + 1) d (j + 1)
        (Twist.subsingleton_cohomology_of_lt R (m + 1) d hgt)

end Headline
p2m_reactivate "P2MW.S_ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist"

end ProjSpaceCech
p2m_reactivate "P2MW.S_ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist P2MW.S_ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech"

theorem solution (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (i : ℕ) :
    Module.Finite R (ProjSpaceCech.Twist.H R n d i) :=
  ProjSpaceCech.Twist.finite_cohomology R n d i

end
p2m_reactivate "P2MW.S_ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech.Twist P2MW.S_ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech"

end S_ProjSpaceCech_Twist_finite_cohomology
end P2MW
export P2MW.S_ProjSpaceCech_Twist_finite_cohomology (solution)
