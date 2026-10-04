-- Prove2me | solution 2 for Schnir.mann
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:02:49.780329+00:00
-- url     : https://prove2.me/submissions/65855894-4f63-4549-861b-5187dfab1eb5

import Mathlib.Combinatorics.Schnirelmann
import Mathlib.Tactic.Linarith

/-!
# Mann's theorem on the Schnirelmann density of sumsets

`σ(A + B) ≥ min 1 (σ A + σ B)` for sets of naturals containing `0`.

The proof is Dyson's (1945), following the exposition of
Nathanson, *Additive number theory and the Dyson transform*, arXiv:2407.12253,
specialized to rank `h = 2`.
-/

open Finset Pointwise Classical

namespace MannAux

/-! ### The counting function -/

/-- `cnt X m = |X ∩ {1, …, m}|`. -/
noncomputable def cnt (X : Set ℕ) [DecidablePred (· ∈ X)] (m : ℕ) : ℕ :=
  ((Ioc 0 m).filter (fun a => a ∈ X)).card

variable {X : Set ℕ} [DecidablePred (· ∈ X)]

theorem cnt_mono {m m' : ℕ} (h : m ≤ m') : cnt X m ≤ cnt X m' := by
  simp only [cnt]
  refine card_mono ?_
  intro a ha
  simp only [mem_filter] at ha ⊢
  exact ⟨Ioc_subset_Ioc (Nat.zero_le 0) h ha.1, ha.2⟩

theorem cnt_zero : cnt X 0 = 0 := by simp [cnt]

theorem cnt_split {k m : ℕ} (hkm : k ≤ m) :
    cnt X m = cnt X k + ((Ioc k m).filter (fun a => a ∈ X)).card := by
  have hio : Ioc 0 m = Ioc 0 k ∪ Ioc k m := by
    ext a
    simp only [mem_Ioc, Finset.mem_union]
    omega
  have hdisj : Disjoint ((Ioc 0 k).filter (fun a => a ∈ X))
      ((Ioc k m).filter (fun a => a ∈ X)) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    simp only [mem_filter, mem_Ioc] at ha hb
    omega
  simp only [cnt]
  rw [hio, Finset.filter_union, Finset.card_union_of_disjoint hdisj]

theorem card_filter_Ioc_le {Y : Set ℕ} [DecidablePred (· ∈ Y)] (hXY : X ⊆ Y) (k m : ℕ) :
    ((Ioc k m).filter (fun a => a ∈ X)).card ≤ ((Ioc k m).filter (fun a => a ∈ Y)).card := by
  refine card_mono ?_
  intro a ha
  simp only [mem_filter] at ha ⊢
  exact ⟨ha.1, hXY ha.2⟩

theorem cnt_sdiff_add {T Y : Set ℕ} [DecidablePred (· ∈ Y \ T)] [DecidablePred (· ∈ T)]
    [DecidablePred (· ∈ Y)] (hTY : T ⊆ Y) (m : ℕ) :
    cnt (Y \ T) m + cnt T m = cnt Y m := by
  have hunion : (Ioc 0 m).filter (fun a => a ∈ Y)
      = (Ioc 0 m).filter (fun a => a ∈ Y \ T) ∪ (Ioc 0 m).filter (fun a => a ∈ T) := by
    ext a
    simp only [mem_filter, Finset.mem_union, Set.mem_sdiff]
    by_cases h : a ∈ T
    · simp [hTY h, h]
    · simp [h]
  have hdisj : Disjoint ((Ioc 0 m).filter (fun a => a ∈ Y \ T))
      ((Ioc 0 m).filter (fun a => a ∈ T)) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hsub
    simp only [mem_filter, Set.mem_sdiff] at ha hb
    subst hsub
    exact ha.2.2 hb.2
  simp only [cnt]
  rw [hunion, Finset.card_union_of_disjoint hdisj]

/-! ### The Dyson transform data -/

/-- The set `T` of elements of `B ∩ [1,n]` that would move past `a₀` out of `A`. -/
def Tset (A B : Set ℕ) (n a₀ : ℕ) : Set ℕ :=
  {c | c ∈ B ∧ 1 ≤ c ∧ c ≤ n ∧ (a₀ + c ≤ n → a₀ + c ∉ A)}

/-- `A' = A ∪ (a₀ + T)`. -/
def Ap (A B : Set ℕ) (n a₀ : ℕ) : Set ℕ := A ∪ (fun c => a₀ + c) '' Tset A B n a₀

/-- `B' = B \ T`. -/
def Bp (A B : Set ℕ) (n a₀ : ℕ) : Set ℕ := B \ Tset A B n a₀

theorem mem_Tset {A B : Set ℕ} {n a₀ c : ℕ} :
    c ∈ Tset A B n a₀ ↔ c ∈ B ∧ 1 ≤ c ∧ c ≤ n ∧ (a₀ + c ≤ n → a₀ + c ∉ A) := Iff.rfl

theorem Tset_subset_B (A B : Set ℕ) (n a₀ : ℕ) : Tset A B n a₀ ⊆ B := fun _ h => h.1

theorem zero_notMem_Tset (A B : Set ℕ) (n a₀ : ℕ) : 0 ∉ Tset A B n a₀ :=
  fun h => absurd h.2.1 (by omega)

theorem mem_Ap_iff {A B : Set ℕ} {n a₀ x : ℕ} :
    x ∈ Ap A B n a₀ ↔ x ∈ A ∨ ∃ t, t ∈ Tset A B n a₀ ∧ a₀ + t = x := by
  rw [Ap, Set.mem_union, Set.mem_image]

/-- `cnt` is extensional. -/
theorem cnt_congr {T Y : Set ℕ} [DecidablePred (· ∈ T)] [DecidablePred (· ∈ Y)]
    (h : ∀ a, a ∈ T ↔ a ∈ Y) (m : ℕ) : cnt T m = cnt Y m := by
  simp only [cnt]
  apply congrArg Finset.card
  ext a
  simp only [mem_filter]
  exact ⟨fun ha => ⟨ha.1, (h a).1 ha.2⟩, fun ha => ⟨ha.1, (h a).2 ha.2⟩⟩

/-! ### The key inclusion `A' + B' ⊆ A + B` on `[1, n]` -/

theorem inclusion_mem (A B : Set ℕ) (n a₀ : ℕ) (hA : 0 ∈ A) (ha₀A : a₀ ∈ insert 0 A) :
    ∀ p, 1 ≤ p → p ≤ n → p ∈ Ap A B n a₀ + Bp A B n a₀ → p ∈ A + B := by
  intro p hp1 hpn hp
  rw [Set.mem_add] at hp
  obtain ⟨x, hx, y, hy, rfl⟩ := hp
  rw [Set.mem_add]
  rcases mem_Ap_iff.1 hx with hxA | ⟨t, ht, hxt⟩
  · exact ⟨x, hxA, y, (Set.mem_sdiff y).1 hy |>.1, rfl⟩
  · have htB : t ∈ B := (mem_Tset.1 ht).1
    rcases (Set.mem_sdiff y).1 hy with ⟨hyB, hyT⟩
    rcases Nat.eq_zero_or_pos y with rfl | hy1
    · rcases Set.mem_insert_iff.1 ha₀A with rfl | ha₀A'
      · exact ⟨0, hA, t, htB, by simp [hxt]⟩
      · exact ⟨a₀, ha₀A', t, htB, by simp [hxt]⟩
    · have hyn : y ≤ n := by omega
      have ha₀yA : a₀ + y ∈ A := by
        by_contra hcon
        exact hyT (mem_Tset.2 ⟨hyB, hy1, hyn, fun _ => hcon⟩)
      exact ⟨a₀ + y, ha₀yA, t, htB, by rw [← hxt]; omega⟩

theorem inclusion_cnt (A B : Set ℕ) (n a₀ : ℕ) [DecidablePred (· ∈ Ap A B n a₀ + Bp A B n a₀)]
    [DecidablePred (· ∈ A + B)] (hA : 0 ∈ A) (ha₀A : a₀ ∈ insert 0 A) :
    cnt (Ap A B n a₀ + Bp A B n a₀) n ≤ cnt (A + B) n := by
  refine card_mono ?_
  intro p hp
  have hio := mem_Ioc.1 (mem_filter.1 hp).1
  exact mem_filter.2 ⟨mem_filter.1 hp |>.1,
    inclusion_mem A B n a₀ hA ha₀A p hio.1 hio.2 (mem_filter.1 hp).2⟩

/-! ### The minimality (Dyson) counting lemma -/

theorem minimal_count (A B : Set ℕ) [DecidablePred (· ∈ A)] {n a₀ : ℕ}
    (hmin : ∀ a < a₀, a ∈ insert 0 A → ∀ c ∈ B, 1 ≤ c → c ≤ n → a + c ≤ n → a + c ∈ A)
    {m c : ℕ} (hcB : c ∈ B) (hc1 : 1 ≤ c) (hcm : c ≤ m) (hmn : m ≤ n) (hlt : m < a₀ + c) :
    cnt A (m - c) + 1 + cnt A (c - 1) ≤ cnt A m := by
  have ha₀pos : 0 < a₀ := by omega
  have hcA : c ∈ A := by
    simpa using hmin 0 ha₀pos (by simp) c hcB hc1 (by omega) (by omega)
  -- the shifted copy of `A ∩ [1, m - c]`
  have himg : (((Ioc 0 (m - c)).filter (fun a => a ∈ A)).image (fun a => a + c))
      ⊆ (Ioc 0 m).filter (fun a => a ∈ A) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := Finset.mem_image.1 hx
    have hio := mem_Ioc.1 (mem_filter.1 ha).1
    have haA : a ∈ A := (mem_filter.1 ha).2
    have hacaA : a + c ∈ A :=
      hmin a (by omega) (by simp [haA]) c hcB hc1 (by omega) (by omega)
    have hxsc : x = a + c := hxa.symm
    subst hxsc
    exact mem_filter.2 ⟨mem_Ioc.2 ⟨by omega, by omega⟩, hacaA⟩
  have himgcard : (((Ioc 0 (m - c)).filter (fun a => a ∈ A)).image (fun a => a + c)).card
      = cnt A (m - c) := Finset.card_image_of_injective _ (fun x1 x2 h => by omega)
  -- `{c} ∪ image` is disjoint from `A ∩ [1, c-1]`, and all of it lies in `A ∩ [1, m]`
  have hnotin : c ∉ (((Ioc 0 (m - c)).filter (fun a => a ∈ A)).image (fun a => a + c)) := by
    intro hcim
    obtain ⟨a, ha, hxa⟩ := Finset.mem_image.1 hcim
    have hio := mem_Ioc.1 (mem_filter.1 ha).1
    omega
  have hdisj : Disjoint ((Ioc 0 (c - 1)).filter (fun a => a ∈ A))
      (insert c (((Ioc 0 (m - c)).filter (fun a => a ∈ A)).image (fun a => a + c))) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy hxy
    subst hxy
    have hxio := mem_Ioc.1 (mem_filter.1 hx).1
    rcases Finset.mem_insert.1 hy with rfl | hy'
    · omega
    · obtain ⟨a, ha, hxa⟩ := Finset.mem_image.1 hy'
      have hio := mem_Ioc.1 (mem_filter.1 ha).1
      omega
  have hsub : ((Ioc 0 (c - 1)).filter (fun a => a ∈ A)) ∪
      (insert c (((Ioc 0 (m - c)).filter (fun a => a ∈ A)).image (fun a => a + c)))
      ⊆ (Ioc 0 m).filter (fun a => a ∈ A) := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · have hio := mem_Ioc.1 (mem_filter.1 h).1
      exact mem_filter.2 ⟨mem_Ioc.2 ⟨hio.1, by omega⟩, (mem_filter.1 h).2⟩
    · rcases Finset.mem_insert.1 h with rfl | h'
      · exact mem_filter.2 ⟨mem_Ioc.2 ⟨hc1, by omega⟩, hcA⟩
      · exact himg h'
  calc cnt A (m - c) + 1 + cnt A (c - 1)
      = cnt A (c - 1) + (cnt A (m - c) + 1) := by omega
    _ = cnt A (c - 1) + (insert c (((Ioc 0 (m - c)).filter (fun a => a ∈ A)).image
          (fun a => a + c))).card := by
          rw [Finset.card_insert_of_notMem hnotin, himgcard]
    _ = (((Ioc 0 (c - 1)).filter (fun a => a ∈ A)) ∪
          (insert c (((Ioc 0 (m - c)).filter (fun a => a ∈ A)).image
            (fun a => a + c)))).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ cnt A m := card_mono hsub

/-! ### The gain `A'(m) ≥ A(m) + T(m - a₀)` -/

theorem cnt_Ap (A B : Set ℕ) (n a₀ m : ℕ) [DecidablePred (· ∈ A)]
    [DecidablePred (· ∈ Tset A B n a₀)] [DecidablePred (· ∈ Ap A B n a₀)] (hmn : m ≤ n) :
    cnt A m + cnt (Tset A B n a₀) (m - a₀) ≤ cnt (Ap A B n a₀) m := by
  have hnew : ∀ t ∈ Tset A B n a₀, a₀ + t ≤ m → a₀ + t ∉ A := by
    intro t ht hle
    exact (mem_Tset.1 ht).2.2.2 (le_trans hle hmn)
  have himgs : (((Ioc 0 (m - a₀)).filter (fun c => c ∈ Tset A B n a₀)).image (fun c => a₀ + c))
      ⊆ (Ioc 0 m).filter (fun x => x ∈ Ap A B n a₀) := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := Finset.mem_image.1 hx
    have hio := mem_Ioc.1 (mem_filter.1 ht).1
    have hxsc : x = a₀ + t := hxt.symm
    subst hxsc
    exact mem_filter.2 ⟨mem_Ioc.2 ⟨by omega, by omega⟩,
      mem_Ap_iff.2 (Or.inr ⟨t, (mem_filter.1 ht).2, rfl⟩)⟩
  have hdisj : Disjoint ((Ioc 0 m).filter (fun x => x ∈ A))
      (((Ioc 0 (m - a₀)).filter (fun c => c ∈ Tset A B n a₀)).image (fun c => a₀ + c)) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy hxy
    rw [← hxy] at hy
    obtain ⟨t, ht, hxt⟩ := Finset.mem_image.1 hy
    have hio := mem_Ioc.1 (mem_filter.1 ht).1
    have hxio := mem_Ioc.1 (mem_filter.1 hx).1
    have hxsc : x = a₀ + t := hxt.symm
    subst hxsc
    exact hnew t (mem_filter.1 ht).2 (by omega) (mem_filter.1 hx).2
  have himgcard : (((Ioc 0 (m - a₀)).filter (fun c => c ∈ Tset A B n a₀)).image
      (fun c => a₀ + c)).card = cnt (Tset A B n a₀) (m - a₀) :=
    Finset.card_image_of_injective _ (fun x1 x2 h => by omega)
  have hsub : ((Ioc 0 m).filter (fun x => x ∈ A)) ∪
      (((Ioc 0 (m - a₀)).filter (fun c => c ∈ Tset A B n a₀)).image (fun c => a₀ + c))
      ⊆ (Ioc 0 m).filter (fun x => x ∈ Ap A B n a₀) := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact mem_filter.2 ⟨(mem_filter.1 h).1, mem_Ap_iff.2 (Or.inl (mem_filter.1 h).2)⟩
    · exact himgs h
  calc cnt A m + cnt (Tset A B n a₀) (m - a₀)
      = ((Ioc 0 m).filter (fun x => x ∈ A)).card + cnt (Tset A B n a₀) (m - a₀) := rfl
    _ = ((Ioc 0 m).filter (fun x => x ∈ A)).card + (((Ioc 0 (m - a₀)).filter
          (fun c => c ∈ Tset A B n a₀)).image (fun c => a₀ + c)).card := by rw [himgcard]
    _ = (((Ioc 0 m).filter (fun x => x ∈ A)) ∪ (((Ioc 0 (m - a₀)).filter
          (fun c => c ∈ Tset A B n a₀)).image (fun c => a₀ + c))).card :=
          (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ cnt (Ap A B n a₀) m := card_mono hsub

/-! ### Dyson's inequality at rank 2, by induction on `B ∩ [1,n]` -/

theorem dyson_core (A B : Set ℕ) (γ : ℝ) (n : ℕ) (hA : 0 ∈ A) (hB : 0 ∈ B)
    (hcount : ∀ w, w ≤ n → γ * w ≤ (cnt A w : ℝ) + cnt B w) :
    (min 1 γ) * n ≤ (cnt (A + B) n : ℝ) := by
  classical
  have main : ∀ (k : ℕ) (γ : ℝ) (X Y : Set ℕ), 0 ∈ X → 0 ∈ Y → cnt Y n = k →
      (∀ w, w ≤ n → γ * w ≤ (cnt X w : ℝ) + cnt Y w) →
      (min 1 γ) * n ≤ (cnt (X + Y) n : ℝ) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k IH =>
      intro γ X Y hX hY hk hXY
      rcases Nat.eq_zero_or_pos k with hk0 | hk1
      · -- base case: `Y ∩ [1,n] = ∅`, so `X + Y = X` on `[1,n]`
        have hempty : (Ioc 0 n).filter (fun a => a ∈ X + Y)
            = (Ioc 0 n).filter (fun a => a ∈ X) := by
          ext p
          simp only [mem_filter, mem_Ioc, Set.mem_add]
          constructor
          · rintro ⟨hp, x, hx, y, hy, rfl⟩
            refine ⟨hp, ?_⟩
            rcases Nat.eq_zero_or_pos y with rfl | hy1
            · exact hx
            · exfalso
              have hyf : y ∈ (Ioc 0 n).filter (fun a => a ∈ Y) :=
                mem_filter.2 ⟨mem_Ioc.2 ⟨hy1, by omega⟩, hy⟩
              simp only [cnt] at hk
              rw [hk0, Finset.card_eq_zero] at hk
              rw [hk] at hyf
              exact absurd hyf (by simp)
          · rintro ⟨hp, hx⟩
            exact ⟨hp, p, hx, 0, hY, by simp⟩
        have hcard : (cnt (X + Y) n : ℝ) = (cnt X n : ℝ) := by
          simp only [cnt, hempty]
        rw [hcard]
        rcases Nat.eq_zero_or_pos n with rfl | hn1
        · simp
        · have h1 := hXY n (le_refl n)
          rw [hk0] at hk
          have h2 : (cnt Y n : ℝ) = 0 := by exact_mod_cast hk
          nlinarith [h1, h2, min_le_right 1 γ]
      · -- step: pick an element of `Y ∩ [1,n]`, find the least Dyson pair, transform
        obtain ⟨c₁, hc₁B, hc₁1, hc₁n⟩ : ∃ c, c ∈ Y ∧ 1 ≤ c ∧ c ≤ n := by
          have hp : 0 < cnt Y n := by rw [hk]; omega
          simp only [cnt] at hp
          obtain ⟨c, hcm⟩ := Finset.card_pos.1 hp
          have hio := mem_Ioc.1 (mem_filter.1 hcm).1
          exact ⟨c, (mem_filter.1 hcm).2, hio.1, hio.2⟩
        -- no infinite ascent: some a ∈ insert 0 X, a ≤ n, blocks c₁
        have hascent : ∀ d : ℕ, ∀ a : ℕ, a ∈ insert 0 X → a ≤ n → n - a = d →
            ∃ a', a' ∈ insert 0 X ∧ a ≤ a' ∧ a' ≤ n ∧ (a' + c₁ ≤ n → a' + c₁ ∉ X) := by
          intro d
          induction d using Nat.strongRecOn with
          | ind d IHd =>
            intro a ha hann hsub
            by_cases hcase : a + c₁ ≤ n ∧ a + c₁ ∈ X
            · obtain ⟨hc1, hc2⟩ := hcase
              obtain ⟨a', ha'm, hle, ha'n, hprop⟩ :=
                IHd (n - (a + c₁)) (by omega) (a + c₁) (by simp [hc2]) (by omega) (by omega)
              exact ⟨a', ha'm, by omega, ha'n, hprop⟩
            · push_neg at hcase
              exact ⟨a, ha, le_rfl, hann, fun hcon => hcase hcon⟩
        obtain ⟨a₀₀, ha₀₀mem, _, ha₀₀n, ha₀₀prop⟩ :=
          hascent (n - 0) 0 (by simp) (by omega) (by omega)
        -- the least such `a₀`
        have hex : ∃ a : ℕ, a ∈ insert 0 X ∧
            ∃ c, c ∈ Y ∧ 1 ≤ c ∧ c ≤ n ∧ (a + c ≤ n → a + c ∉ X) :=
          ⟨a₀₀, ha₀₀mem, c₁, hc₁B, hc₁1, hc₁n, ha₀₀prop⟩
        obtain ⟨a₀, ⟨ha₀mem, hc₀⟩, ha₀min⟩ := Nat.findX hex
        obtain ⟨c₀, c₀B, c₀1, c₀n, c₀P⟩ := hc₀
        have ha₀n : a₀ ≤ n := by
          by_contra hcon
          exact ha₀min a₀₀ (by omega) ⟨ha₀₀mem, ⟨c₁, hc₁B, hc₁1, hc₁n, ha₀₀prop⟩⟩
        have hmin : ∀ a < a₀, a ∈ insert 0 X →
            ∀ c ∈ Y, 1 ≤ c → c ≤ n → a + c ≤ n → a + c ∈ X := by
          intro a ha1 ha2 c hcY hc1 hcn hac
          by_contra hcon
          exact ha₀min a ha1 ⟨ha2, ⟨c, hcY, hc1, hcn, fun _ => hcon⟩⟩
        -- the transform moves at least one element of `Y`
        have hTn : 1 ≤ cnt (Tset X Y n a₀) n := by
          have hc₀mem : c₀ ∈ (Ioc 0 n).filter (fun a => a ∈ Tset X Y n a₀) :=
            mem_filter.2 ⟨mem_Ioc.2 ⟨c₀1, c₀n⟩, mem_Tset.2 ⟨c₀B, c₀1, c₀n, c₀P⟩⟩
          simp only [cnt]
          exact Finset.card_pos.2 ⟨c₀, hc₀mem⟩
        -- pin classical decidability for the composite sets used below, so that all
        -- counting statements agree with the instances in `main`'s statement
        letI instSD : DecidablePred (· ∈ Y \ Tset X Y n a₀) :=
          fun a => Classical.propDecidable (a ∈ Y \ Tset X Y n a₀)
        letI instSS : DecidablePred (· ∈ Ap X Y n a₀ + (Y \ Tset X Y n a₀)) :=
          fun a => Classical.propDecidable (a ∈ Ap X Y n a₀ + (Y \ Tset X Y n a₀))
        have hsdn : cnt (Y \ Tset X Y n a₀) n + cnt (Tset X Y n a₀) n = cnt Y n :=
          cnt_sdiff_add (Tset_subset_B X Y n a₀) n
        have hBplt : cnt (Y \ Tset X Y n a₀) n < k := by omega
        -- the no-bad-z lemma
        have nobadz : ∀ z, z < a₀ → (min 1 γ) * z ≤ (cnt X z : ℝ) := by
          intro z
          induction z using Nat.strongRecOn with
          | ind z IH =>
            intro hz
            rcases Nat.eq_zero_or_pos z with rfl | hz1
            · simp [cnt_zero]
            · by_contra hlt
              push_neg at hlt
              have hcz : γ * z ≤ (cnt X z : ℝ) + cnt Y z := hXY z (by omega)
              have hYpos : 0 < cnt Y z := by
                by_contra hc
                push_neg at hc
                have hcle : (cnt Y z : ℝ) ≤ 0 := by exact_mod_cast hc
                have hznn : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
                nlinarith [hcz, min_le_right 1 γ, hlt, hznn]
              obtain ⟨c, hcY, hc1, hczle⟩ : ∃ c, c ∈ Y ∧ 1 ≤ c ∧ c ≤ z := by
                simp only [cnt] at hYpos
                obtain ⟨c, hcm⟩ := Finset.card_pos.1 hYpos
                have hio := mem_Ioc.1 (mem_filter.1 hcm).1
                exact ⟨c, (mem_filter.1 hcm).2, hio.1, hio.2⟩
              have h6 := minimal_count X Y hmin hcY hc1 hczle (by omega) (by omega)
              have e1 : (min 1 γ) * (((z - c : ℕ) : ℝ)) ≤ (cnt X (z - c) : ℝ) :=
                IH (z - c) (by omega) (by omega)
              have e2 : (min 1 γ) * (((c - 1 : ℕ) : ℝ)) ≤ (cnt X (c - 1) : ℝ) :=
                IH (c - 1) (by omega) (by omega)
              have h6r : (((cnt X (z - c) : ℕ) : ℝ) + 1 + ((cnt X (c - 1) : ℕ) : ℝ))
                  ≤ (cnt X z : ℝ) := by exact_mod_cast h6
              have key : (((z - c : ℕ) : ℝ) + ((c - 1 : ℕ) : ℝ) + 1) = (z : ℝ) := by
                exact_mod_cast (by omega : (z - c : ℕ) + (c - 1 : ℕ) + 1 = z)
              have key2 : (min 1 γ) * ((z : ℕ) : ℝ)
                  = (min 1 γ) * ((z - c : ℕ) : ℝ) + (min 1 γ) * ((c - 1 : ℕ) : ℝ)
                    + (min 1 γ) := by rw [← key]; ring
              nlinarith [h6r, e1, e2, min_le_left 1 γ, key2]
        -- the transformed counting bound
        have hcount' : ∀ w, w ≤ n →
            (min 1 γ) * w ≤ (cnt (Ap X Y n a₀) w : ℝ) + cnt (Y \ Tset X Y n a₀) w := by
          intro w hw
          have hApLB := cnt_Ap X Y n a₀ w hw
          have hsd : cnt (Y \ Tset X Y n a₀) w + cnt (Tset X Y n a₀) w = cnt Y w :=
            cnt_sdiff_add (Tset_subset_B X Y n a₀) w
          have hspT := cnt_split (X := Tset X Y n a₀) (Nat.sub_le w a₀)
          have hspY := cnt_split (X := Y) (Nat.sub_le w a₀)
          have hiTle := card_filter_Ioc_le (Tset_subset_B X Y n a₀) (w - a₀) w
          rcases Nat.lt_or_ge (cnt (Tset X Y n a₀) (w - a₀)) (cnt (Tset X Y n a₀) w) with hlt | hge
          · -- the interesting case: some element of `T` lies in `(w - a₀, w]`
            have htex : ∃ t, t ∈ Tset X Y n a₀ ∧ w - a₀ < t ∧ t ≤ w := by
              by_contra hcon
              push_neg at hcon
              have hfeq : (Ioc 0 w).filter (fun a => a ∈ Tset X Y n a₀)
                  = (Ioc 0 (w - a₀)).filter (fun a => a ∈ Tset X Y n a₀) := by
                ext a
                simp only [mem_filter, mem_Ioc]
                constructor
                · rintro ⟨⟨h1, h2⟩, h3⟩
                  refine ⟨⟨h1, ?_⟩, h3⟩
                  by_contra hgt
                  have hcon' := hcon a h3 (by omega)
                  omega
                · rintro ⟨⟨h1, h2⟩, h3⟩
                  exact ⟨⟨h1, by omega⟩, h3⟩
              simp only [cnt, hfeq] at hlt
              omega
            obtain ⟨t, ht, htw, httw⟩ := htex
            have hbex : ∃ b : ℕ, b ∈ Y ∧ w - a₀ < b ∧ b ≤ w :=
              ⟨t, (mem_Tset.1 ht).1, htw, httw⟩
            obtain ⟨b, ⟨hbY, hbw⟩, hbmin⟩ := Nat.findX hbex
            have hb1 : 1 ≤ b := by omega
            have hbw1 : b ≤ w := hbw.2
            have hbnole : ∀ c, c ∈ Y → w - a₀ < c → c < b → False := by
              intro c hcY hcw hcb
              exact hbmin c (by omega) ⟨hcY, hcw, by omega⟩
            have hcntb : cnt Y (b - 1) = cnt Y (w - a₀) := by
              apply le_antisymm ?_ (cnt_mono (by omega))
              simp only [cnt]
              refine card_mono ?_
              intro c hc
              have hio := mem_Ioc.1 (mem_filter.1 hc).1
              refine mem_filter.2 ⟨mem_Ioc.2 ⟨hio.1, ?_⟩, (mem_filter.1 hc).2⟩
              by_contra hcon
              exact hbnole c (mem_filter.1 hc).2 (by omega) (by omega)
            have h6 := minimal_count X Y hmin hbY hb1 hbw1 (by omega) (by omega)
            have hγb : γ * (((b - 1 : ℕ) : ℝ)) ≤ (cnt X (b - 1) : ℝ) + cnt Y (b - 1) :=
              hXY (b - 1) (by omega)
            have hδwb : (min 1 γ) * (((w - b : ℕ) : ℝ)) ≤ (cnt X (w - b) : ℝ) := by
              rcases Nat.eq_zero_or_pos (w - b) with h0 | h1
              · rw [h0]; simp [cnt_zero]
              · exact nobadz (w - b) (by omega)
            have h6r : (((cnt X (w - b) : ℕ) : ℝ) + 1 + ((cnt X (b - 1) : ℕ) : ℝ))
                ≤ (cnt X w : ℝ) := by exact_mod_cast h6
            have key : (((w - b : ℕ) : ℝ) + ((b - 1 : ℕ) : ℝ) + 1) = (w : ℝ) := by
              exact_mod_cast (by omega : (w - b : ℕ) + (b - 1 : ℕ) + 1 = w)
            have key2 : (min 1 γ) * ((w : ℕ) : ℝ)
                = (min 1 γ) * ((w - b : ℕ) : ℝ) + (min 1 γ) * ((b - 1 : ℕ) : ℝ)
                  + (min 1 γ) := by rw [← key]; ring
            have hb1nn : (0 : ℝ) ≤ ((b - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
            rify at hApLB hsd hspT hspY hiTle hcntb
            nlinarith [hApLB, hsd, hspT, hspY, hiTle, hcntb, h6r, hγb, hδwb, key2, hb1nn,
              min_le_left 1 γ, min_le_right 1 γ]
          · -- the easy case: `T ∩ [1, w] = T ∩ [1, w - a₀]`
            have hTeq : cnt (Tset X Y n a₀) w = cnt (Tset X Y n a₀) (w - a₀) :=
              le_antisymm hge (cnt_mono (Nat.sub_le w a₀))
            have hγw : γ * w ≤ (cnt X w : ℝ) + cnt Y w := hXY w hw
            rify at hApLB hsd hTeq
            nlinarith [hApLB, hsd, hTeq, hγw, min_le_right 1 γ]
        -- apply the induction hypothesis to the transform
        have hAp0 : 0 ∈ Ap X Y n a₀ := Or.inl hX
        have hBp0 : 0 ∈ Y \ Tset X Y n a₀ :=
          (Set.mem_sdiff 0).2 ⟨hY, zero_notMem_Tset X Y n a₀⟩
        have hIH := IH (cnt (Y \ Tset X Y n a₀) n) hBplt (min 1 γ)
          (Ap X Y n a₀) (Y \ Tset X Y n a₀) hAp0 hBp0 rfl hcount'
        have hinc : cnt (Ap X Y n a₀ + (Y \ Tset X Y n a₀)) n ≤ cnt (X + Y) n :=
          inclusion_cnt X Y n a₀ hX ha₀mem
        have hmmm : min 1 (min 1 γ) = min 1 γ := min_eq_right (min_le_left 1 γ)
        rw [hmmm] at hIH
        have hincr : ((cnt (Ap X Y n a₀ + (Y \ Tset X Y n a₀)) n : ℕ) : ℝ)
            ≤ (cnt (X + Y) n : ℝ) := by exact_mod_cast hinc
        nlinarith [hIH, hincr]
  exact main (cnt B n) γ A B hA hB rfl hcount

end MannAux

open Finset Pointwise Classical

open Pointwise Classical in
/-- Mann's theorem: the Schnirelmann density is superadditive up to `1`. -/
theorem solution (D E : Set ℕ) (hD : 0 ∈ D) (hE : 0 ∈ E) :
    min 1 (schnirelmannDensity D + schnirelmannDensity E) ≤ schnirelmannDensity (D + E) := by
  rw [le_schnirelmannDensity_iff]
  intro n hn
  have hcount : ∀ w, w ≤ n → (schnirelmannDensity D + schnirelmannDensity E) * w
      ≤ (MannAux.cnt D w : ℝ) + MannAux.cnt E w := by
    intro w hw
    have h1 : schnirelmannDensity D * w ≤ (MannAux.cnt D w : ℝ) :=
      schnirelmannDensity_mul_le_card_filter
    have h2 : schnirelmannDensity E * w ≤ (MannAux.cnt E w : ℝ) :=
      schnirelmannDensity_mul_le_card_filter
    nlinarith [h1, h2]
  have hfin := MannAux.dyson_core D E (schnirelmannDensity D + schnirelmannDensity E) n hD hE hcount
  rw [le_div_iff₀ (by exact_mod_cast hn)]
  exact hfin
