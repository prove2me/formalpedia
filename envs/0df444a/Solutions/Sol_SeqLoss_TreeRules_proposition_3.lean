-- Prove2me | solution 1 for SeqLoss.TreeRules.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T20:03:10.784313+00:00
-- url     : https://prove2.me/submissions/4ab45e92-3bfc-4652-a3cc-faa4024840a7

import Mathlib
import Definitions.Def_SeqLoss_TreeRules_Setting
import Definitions.Def_SeqLoss_TreeRules_Axioms

set_option autoImplicit false

open SeqLoss.TreeRules

namespace SeqLossP3

/-- The unit loss on the edge `e`. -/
def unitLoss (e : ℕ × ℕ) : ℕ × ℕ → ℝ := fun e' => if e' = e then 1 else 0

/-! ### PartA -/
/-- (A1) A rule only sees the loss on the edges of the tree (label invariance with `π = id`). -/
theorem phi_congr_loss (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ) (hφ : IsTreeRule φ)
    {T : Finset (ℕ × ℕ)} (hT : IsTree T) {ℓ ℓ' : ℕ × ℕ → ℝ} (hℓ : IsTreeLoss ℓ)
    (hℓ' : IsTreeLoss ℓ') (h : ∀ e ∈ T, ℓ e = ℓ' e) :
    ∀ i ∈ N T, φ T ℓ i = φ T ℓ' i := by
  intro i hi
  have h3 := (hφ T hT ℓ hℓ).2.2.1 (Equiv.refl ℕ) ℓ' hℓ'
    (fun e he => by simpa using (h e he).symm) i hi
  have hrel : relabel (Equiv.refl ℕ) T = T := by
    ext x
    simp [relabel]
  simpa [hrel] using h3

/-- Cauchy's functional equation on `[0, ∞)` for a nonnegative additive function. -/
theorem PA_cauchy (g : ℝ → ℝ) (hadd : ∀ a b, 0 ≤ a → 0 ≤ b → g a + g b = g (a + b))
    (hnn : ∀ a, 0 ≤ a → 0 ≤ g a) : ∀ a, 0 ≤ a → g a = a * g 1 := by
  have h0 : g 0 = 0 := by
    have := hadd 0 0 le_rfl le_rfl
    rw [add_zero] at this
    linarith
  have hmono : ∀ a b, 0 ≤ a → a ≤ b → g a ≤ g b := by
    intro a b ha hab
    have := hadd a (b - a) ha (by linarith)
    rw [add_sub_cancel] at this
    linarith [hnn (b - a) (by linarith)]
  have hmul : ∀ (n : ℕ) (a : ℝ), 0 ≤ a → g (n * a) = n * g a := by
    intro n a ha
    induction n with
    | zero => simp [h0]
    | succ k ih =>
      have := hadd (k * a) a (by positivity) ha
      push_cast
      rw [add_mul, one_mul, ← this, ih]
      ring
  intro a ha
  set c := g 1 with hcdef
  have hc : 0 ≤ c := hnn 1 zero_le_one
  have key : ∀ n : ℕ, (n : ℝ) * |g a - a * c| ≤ c := by
    intro n
    set k := ⌊(n : ℝ) * a⌋₊
    have hk1 : (k : ℝ) ≤ n * a := Nat.floor_le (by positivity)
    have hk2 : (n : ℝ) * a < k + 1 := Nat.lt_floor_add_one _
    have hgk : g k = k * c := by simpa using hmul k 1 zero_le_one
    have hgk1 : g ((k + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) * c := by
      simpa using hmul (k + 1) 1 zero_le_one
    have hna : g (n * a) = n * g a := hmul n a ha
    have l1 : g k ≤ g (n * a) := hmono _ _ (by positivity) hk1
    have l2 : g (n * a) ≤ g ((k + 1 : ℕ) : ℝ) :=
      hmono _ _ (by positivity) (by push_cast; linarith)
    push_cast at hgk1 l2
    rw [← abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), ← abs_mul, abs_le]
    have m1 := mul_le_mul_of_nonneg_right hk1 hc
    have m2 := mul_le_mul_of_nonneg_right hk2.le hc
    constructor <;> nlinarith
  by_contra hne
  have hpos : 0 < |g a - a * c| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (c / |g a - a * c|)
  have := key n
  rw [div_lt_iff₀ hpos] at hn
  linarith

/-- Homogeneity of an additive tree rule on nonnegative scalings of a loss. -/
theorem PA_homog (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ) (hφ : IsTreeRule φ)
    (hadd : TreeAdditive φ) {T : Finset (ℕ × ℕ)} (hT : IsTree T) {μ : ℕ × ℕ → ℝ}
    (hμ : IsTreeLoss μ) {i : ℕ} (hi : i ∈ N T) (a : ℝ) (ha : 0 ≤ a) :
    φ T (a • μ) i = a * φ T μ i := by
  have hsm : ∀ b : ℝ, 0 ≤ b → IsTreeLoss (b • μ) := fun b hb e => by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg hb (hμ e)
  have := PA_cauchy (fun b => φ T (b • μ) i)
    (fun b c hb hc => by
      show φ T (b • μ) i + φ T (c • μ) i = φ T ((b + c) • μ) i
      rw [hadd T hT _ _ (hsm b hb) (hsm c hc) i hi, add_smul])
    (fun b hb => (hφ T hT _ (hsm b hb)).1 i hi) a ha
  simpa using this

/-- (A2) Under tree additivity, liabilities are linear in the loss. -/
theorem phi_decomp (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ) (hφ : IsTreeRule φ)
    (hadd : TreeAdditive φ) {T : Finset (ℕ × ℕ)} (hT : IsTree T) {ℓ : ℕ × ℕ → ℝ}
    (hℓ : IsTreeLoss ℓ) :
    ∀ i ∈ N T, φ T ℓ i = ∑ e ∈ T, ℓ e * φ T (unitLoss e) i := by
  intro i hi
  have hu : ∀ e, IsTreeLoss (unitLoss e) := fun e e' => by
    unfold unitLoss
    split_ifs <;> norm_num
  have hsmul : ∀ e, IsTreeLoss (ℓ e • unitLoss e) := fun e e' => by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (hℓ e) (hu e e')
  have hnn : ∀ S : Finset (ℕ × ℕ), IsTreeLoss (∑ e ∈ S, ℓ e • unitLoss e) := fun S e' => by
    rw [Finset.sum_apply]
    exact Finset.sum_nonneg fun e _ => hsmul e e'
  have hzero : φ T 0 i = 0 := by
    have := hadd T hT 0 0 (fun _ => le_rfl) (fun _ => le_rfl) i hi
    rw [add_zero] at this
    linarith
  have hS : ∀ S : Finset (ℕ × ℕ),
      φ T (∑ e ∈ S, ℓ e • unitLoss e) i = ∑ e ∈ S, ℓ e * φ T (unitLoss e) i := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [hzero]
    | insert e S he ih =>
      rw [Finset.sum_insert he, Finset.sum_insert he,
        ← hadd T hT _ _ (hsmul e) (hnn S) i hi, ih,
        PA_homog φ hφ hadd hT (hu e) hi (ℓ e) (hℓ e)]
  rw [← hS T]
  refine phi_congr_loss φ hφ hT hℓ (hnn T) (fun e he => ?_) i hi
  rw [Finset.sum_apply]
  simp [unitLoss, he]

/-! ### PartB1 -/
lemma PB1_mem_V {T : Finset (ℕ × ℕ)} {v : ℕ} :
    v ∈ V T ↔ (∃ g ∈ T, g.1 = v) ∨ ∃ g ∈ T, g.2 = v := by
  simp [V]

lemma PB1_mem_N {T : Finset (ℕ × ℕ)} {v : ℕ} : v ∈ N T ↔ ∃ g ∈ T, g.1 = v := by
  simp [N]

lemma PB1_fst_mem_V {T : Finset (ℕ × ℕ)} {g : ℕ × ℕ} (hg : g ∈ T) : g.1 ∈ V T :=
  PB1_mem_V.mpr (Or.inl ⟨g, hg, rfl⟩)

lemma PB1_snd_mem_V {T : Finset (ℕ × ℕ)} {g : ℕ × ℕ} (hg : g ∈ T) : g.2 ∈ V T :=
  PB1_mem_V.mpr (Or.inr ⟨g, hg, rfl⟩)

lemma PB1_V_mono {S T : Finset (ℕ × ℕ)} (h : S ⊆ T) : V S ⊆ V T := by
  intro v hv
  rcases PB1_mem_V.mp hv with ⟨g, hg, hgv⟩ | ⟨g, hg, hgv⟩
  · exact PB1_mem_V.mpr (Or.inl ⟨g, h hg, hgv⟩)
  · exact PB1_mem_V.mpr (Or.inr ⟨g, h hg, hgv⟩)

lemma PB1_N_mono {S T : Finset (ℕ × ℕ)} (h : S ⊆ T) : N S ⊆ N T := by
  intro v hv
  obtain ⟨g, hg, hgv⟩ := PB1_mem_N.mp hv
  exact PB1_mem_N.mpr ⟨g, h hg, hgv⟩

lemma PB1_mem_pathTo {T : Finset (ℕ × ℕ)} {v : ℕ} {g : ℕ × ℕ} :
    g ∈ pathTo T v ↔ g ∈ T ∧ Relation.ReflTransGen (Edge T) g.2 v := by
  simp only [pathTo, Finset.mem_filter]

lemma PB1_unitLoss_nonneg (e : ℕ × ℕ) : IsTreeLoss (unitLoss e) := by
  intro x
  unfold unitLoss
  split_ifs <;> norm_num

/-- Trees have no cycles: an edge `(a, b)` cannot be closed by a path from `b` back to `a`. -/
lemma PB1_no_cycle {T : Finset (ℕ × ℕ)} (hT : IsTree T) {a b : ℕ} (hab : (a, b) ∈ T) :
    ¬ Relation.ReflTransGen (Edge T) b a := by
  obtain ⟨r, _, hroot, huniq, hreach⟩ := hT
  have key : ∀ v, Relation.ReflTransGen (Edge T) r v → ¬ Relation.TransGen (Edge T) v v := by
    intro v hv
    induction hv with
    | refl =>
      intro h
      obtain ⟨u, _, hu⟩ := Relation.TransGen.tail'_iff.mp h
      exact hroot (u, r) hu rfl
    | @tail a' b' _ hab' ih =>
      intro hc
      apply ih
      obtain ⟨u, hbu, hub⟩ := Relation.TransGen.tail'_iff.mp hc
      have hab'T : (a', b') ∈ T := hab'
      obtain ⟨w, _, hw⟩ := huniq b' (PB1_snd_mem_V hab'T) (hroot _ hab'T)
      have hua : u = a' := (hw u hub).trans (hw a' hab'T).symm
      subst hua
      exact Relation.TransGen.head' hab' hbu
  intro hba
  exact key a (hreach a (PB1_fst_mem_V (g := (a, b)) hab)) (Relation.TransGen.head' hab hba)

/-- A nonempty, parent-closed subset of a tree is a tree (with the same root). -/
lemma PB1_isTree_of_closed {T S : Finset (ℕ × ℕ)} (hT : IsTree T) (hST : S ⊆ T)
    (hne : S.Nonempty) (hcl : ∀ g ∈ S, ∀ h ∈ T, h.2 = g.1 → h ∈ S) : IsTree S := by
  obtain ⟨r, _, hroot, huniq, hreach⟩ := hT
  have hlift : ∀ v, Relation.ReflTransGen (Edge T) r v → (∀ h ∈ T, h.2 = v → h ∈ S) →
      Relation.ReflTransGen (Edge S) r v := by
    intro v hv
    induction hv with
    | refl => intro _; exact Relation.ReflTransGen.refl
    | @tail a b _ hab ih =>
      intro hb
      have habS : (a, b) ∈ S := hb (a, b) hab rfl
      exact Relation.ReflTransGen.tail (ih (fun h hh h2 => hcl (a, b) habS h hh h2)) habS
  have hInS : ∀ v ∈ V S, ∀ h ∈ T, h.2 = v → h ∈ S := by
    intro v hv h hh h2
    rcases PB1_mem_V.mp hv with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩
    · exact hcl g hg h hh h2
    · have hgT := hST hg
      obtain ⟨w, _, hw⟩ := huniq g.2 (PB1_snd_mem_V hgT) (hroot g hgT)
      have h1 : h.1 = g.1 :=
        (hw h.1 (by rw [← h2]; exact hh)).trans (hw g.1 hgT).symm
      have : h = g := Prod.ext h1 h2
      rw [this]; exact hg
  have hreachS : ∀ v ∈ V S, Relation.ReflTransGen (Edge S) r v := fun v hv =>
    hlift v (hreach v (PB1_V_mono hST hv)) (hInS v hv)
  obtain ⟨g, hg⟩ := hne
  have hrS : r ∈ V S := by
    rcases Relation.ReflTransGen.cases_head (hreachS g.1 (PB1_fst_mem_V hg)) with h | ⟨c, hc, _⟩
    · rw [h]; exact PB1_fst_mem_V hg
    · exact PB1_fst_mem_V (g := (r, c)) hc
  refine ⟨r, hrS, fun g hg => hroot g (hST hg), ?_, hreachS⟩
  intro v hv hvr
  obtain ⟨w, hwT, hw⟩ := huniq v (PB1_V_mono hST hv) hvr
  exact ⟨w, hInS v hv (w, v) hwT rfl, fun y hy => hw y (hST hy)⟩

/-- Along an edge `(a, b)`, the path to the root strictly grows. -/
lemma PB1_card_pathTo_lt {T : Finset (ℕ × ℕ)} (hT : IsTree T) {a b : ℕ} (hab : (a, b) ∈ T) :
    (pathTo T a).card < (pathTo T b).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(a, b), PB1_mem_pathTo.mpr ⟨hab, Relation.ReflTransGen.refl⟩, ?_⟩
    intro h
    exact PB1_no_cycle hT hab (PB1_mem_pathTo.mp h).2
  · intro g hg
    obtain ⟨hgT, hgr⟩ := PB1_mem_pathTo.mp hg
    exact PB1_mem_pathTo.mpr ⟨hgT, Relation.ReflTransGen.tail hgr hab⟩

/-- A path in `T` to `y` all of whose edges (followed by a path to `y`) lie in `T'` is a path
in `T'`. -/
lemma PB1_rtg_lift {T T' : Finset (ℕ × ℕ)} {y : ℕ}
    (h : ∀ a b, (a, b) ∈ T → Relation.ReflTransGen (Edge T) b y → (a, b) ∈ T') :
    ∀ x, Relation.ReflTransGen (Edge T) x y → Relation.ReflTransGen (Edge T') x y := by
  intro x hx
  induction hx using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hac hcy ih => exact Relation.ReflTransGen.head (h _ _ hac hcy) ih

/-- The core of the pruning: on the agents of the path, the liabilities coincide. -/
lemma PB1_main (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ) (hzt : TreeZeroTruncation φ)
    (e : ℕ × ℕ) :
    ∀ T : Finset (ℕ × ℕ), IsTree T → e ∈ T → ∀ i ∈ N (pathTo T e.2),
      φ T (unitLoss e) i = φ (pathTo T e.2) (unitLoss e) i := by
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
  intro hT he i hi
  by_cases hP : pathTo T e.2 = T
  · rw [hP]
  have hsub : pathTo T e.2 ⊆ T := fun g hg => (PB1_mem_pathTo.mp hg).1
  have hek : e ∈ pathTo T e.2 := PB1_mem_pathTo.mpr ⟨he, Relation.ReflTransGen.refl⟩
  obtain ⟨f0, hf0T, hf0P⟩ : ∃ f ∈ T, f ∉ pathTo T e.2 := by
    by_contra hcon
    push Not at hcon
    exact hP (Finset.Subset.antisymm hsub hcon)
  obtain ⟨f, hfQ, hfmax⟩ := Finset.exists_max_image (T.filter (fun f => f ∉ pathTo T e.2))
    (fun f => (pathTo T f.2).card) ⟨f0, Finset.mem_filter.mpr ⟨hf0T, hf0P⟩⟩
  obtain ⟨hfT, hfP⟩ := Finset.mem_filter.mp hfQ
  have hleaf : ∀ g ∈ T, g.1 ≠ f.2 := by
    intro g hg hgf
    have hfg : (f.2, g.2) ∈ T := by rw [← hgf]; exact hg
    have hgP : g ∉ pathTo T e.2 := by
      intro hgP
      apply hfP
      exact PB1_mem_pathTo.mpr ⟨hfT, Relation.ReflTransGen.head hfg (PB1_mem_pathTo.mp hgP).2⟩
    have h1 := hfmax g (Finset.mem_filter.mpr ⟨hg, hgP⟩)
    have h2 := PB1_card_pathTo_lt hT hfg
    omega
  have hfe : f ≠ e := fun h => hfP (h ▸ hek)
  have heT' : e ∈ T.erase f := Finset.mem_erase.mpr ⟨hfe.symm, he⟩
  have hins : insert f (T.erase f) = T := Finset.insert_erase hfT
  have hT' : IsTree (T.erase f) := by
    refine PB1_isTree_of_closed hT (Finset.erase_subset _ _) ⟨e, heT'⟩ ?_
    intro g hg h hh h2
    refine Finset.mem_erase.mpr ⟨?_, hh⟩
    rintro rfl
    exact hleaf g (Finset.erase_subset _ _ hg) h2.symm
  have hf2 : f.2 ∉ V (T.erase f) := by
    intro hv
    rcases PB1_mem_V.mp hv with ⟨g, hg, hgf⟩ | ⟨g, hg, hgf⟩
    · exact hleaf g (Finset.erase_subset _ _ hg) hgf
    · obtain ⟨r, _, hroot, huniq, _⟩ := hT
      obtain ⟨w, _, hw⟩ := huniq f.2 (PB1_snd_mem_V hfT) (hroot f hfT)
      have hgT : g ∈ T := Finset.erase_subset _ _ hg
      have h1 : g.1 = f.1 :=
        (hw g.1 (by rw [← hgf]; exact hgT)).trans (hw f.1 hfT).symm
      exact (Finset.mem_erase.mp hg).1 (Prod.ext h1 hgf)
  have hpath : pathTo (T.erase f) e.2 = pathTo T e.2 := by
    ext g
    rw [PB1_mem_pathTo, PB1_mem_pathTo]
    constructor
    · rintro ⟨hg, hr⟩
      exact ⟨Finset.erase_subset _ _ hg,
        PB1_rtg_lift (fun a b hab _ => Finset.erase_subset f T hab) _ hr⟩
    · rintro ⟨hg, hr⟩
      refine ⟨Finset.mem_erase.mpr ⟨?_, hg⟩, ?_⟩
      · rintro rfl
        exact hfP (PB1_mem_pathTo.mpr ⟨hg, hr⟩)
      · refine PB1_rtg_lift ?_ _ hr
        intro a b hab hb
        refine Finset.mem_erase.mpr ⟨?_, hab⟩
        intro habf
        apply hfP
        rw [← habf]
        exact PB1_mem_pathTo.mpr ⟨hab, hb⟩
  have hi' : i ∈ N (pathTo (T.erase f) e.2) := by rw [hpath]; exact hi
  have hiT' : i ∈ N (T.erase f) :=
    PB1_N_mono (fun g hg => (PB1_mem_pathTo.mp hg).1) hi'
  have h1 := hzt (T.erase f) hT' (unitLoss e) (PB1_unitLoss_nonneg e) f
    (by rw [hins]; exact hT) hf2 (by simp [unitLoss, hfe]) i hiT'
  rw [hins] at h1
  have h2 := ih (T.erase f) (Finset.erase_ssubset hfT) hT' heT' i hi'
  rw [hpath] at h2
  rw [← h1, h2]

/-- (B1) Pruning: under tree zero truncation, a unit loss on `e` is shared as on the path from
the root to `e.2`; agents off that path pay nothing. -/
theorem phi_unit_prune (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ) (hφ : IsTreeRule φ)
    (hzt : TreeZeroTruncation φ) {T : Finset (ℕ × ℕ)} (hT : IsTree T) {e : ℕ × ℕ}
    (he : e ∈ T) :
    IsTree (pathTo T e.2) ∧
    ∀ i ∈ N T, φ T (unitLoss e) i =
      if i ∈ N (pathTo T e.2) then φ (pathTo T e.2) (unitLoss e) i else 0 := by
  have hk : e ∈ pathTo T e.2 := PB1_mem_pathTo.mpr ⟨he, Relation.ReflTransGen.refl⟩
  have hPsub : pathTo T e.2 ⊆ T := fun g hg => (PB1_mem_pathTo.mp hg).1
  have hPT : IsTree (pathTo T e.2) := by
    refine PB1_isTree_of_closed hT hPsub ⟨e, hk⟩ ?_
    intro g hg h hh h2
    have hg' := PB1_mem_pathTo.mp hg
    refine PB1_mem_pathTo.mpr ⟨hh, Relation.ReflTransGen.head ?_ hg'.2⟩
    show (h.2, g.2) ∈ T
    rw [h2]
    exact hg'.1
  refine ⟨hPT, fun i hi => ?_⟩
  have hu := PB1_unitLoss_nonneg e
  have hmain := PB1_main φ hzt e T hT he
  split_ifs with hiP
  · exact hmain i hiP
  · obtain ⟨hnn, hsum, -, -⟩ := hφ T hT (unitLoss e) hu
    obtain ⟨-, hsumP, -, -⟩ := hφ _ hPT (unitLoss e) hu
    have hNsub : N (pathTo T e.2) ⊆ N T := PB1_N_mono hPsub
    have hs1 : ∑ e' ∈ T, unitLoss e e' = 1 := by simp [unitLoss, he]
    have hs2 : ∑ e' ∈ pathTo T e.2, unitLoss e e' = 1 := by simp [unitLoss, hk]
    have hsplit := Finset.sum_sdiff hNsub (f := φ T (unitLoss e))
    have heqP : ∑ j ∈ N (pathTo T e.2), φ T (unitLoss e) j =
        ∑ j ∈ N (pathTo T e.2), φ (pathTo T e.2) (unitLoss e) j :=
      Finset.sum_congr rfl hmain
    have hzero : ∑ j ∈ N T \ N (pathTo T e.2), φ T (unitLoss e) j = 0 := by linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg] at hzero
    · exact hzero i (Finset.mem_sdiff.mpr ⟨hi, hiP⟩)
    · intro j hj
      exact hnn j (Finset.mem_sdiff.mp hj).1

/-! ### PartB2 -/
lemma PB2_mem_V_fst {T : Finset (ℕ × ℕ)} {a b : ℕ} (h : (a, b) ∈ T) : a ∈ V T := by
  unfold V
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(a, b), h, rfl⟩)

lemma PB2_mem_V_snd {T : Finset (ℕ × ℕ)} {a b : ℕ} (h : (a, b) ∈ T) : b ∈ V T := by
  unfold V
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(a, b), h, rfl⟩)

section Tree

variable {T : Finset (ℕ × ℕ)} {r : ℕ}
  (hroot : ∀ e ∈ T, e.2 ≠ r) (huniq : ∀ v ∈ V T, v ≠ r → ∃! u, (u, v) ∈ T)
  (hreach : ∀ v ∈ V T, Relation.ReflTransGen (Edge T) r v)
include hroot huniq

lemma PB2_parent_unique {a b c : ℕ} (hab : (a, b) ∈ T) (hcb : (c, b) ∈ T) : a = c :=
  (huniq b (PB2_mem_V_snd hab) (hroot _ hab)).unique hab hcb

omit huniq in
lemma PB2_to_root {x : ℕ} (h : Relation.ReflTransGen (Edge T) x r) : x = r := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, _, hc⟩
  · exact h.symm
  · exact absurd rfl (hroot _ hc)

lemma PB2_no_cycle {v : ℕ} (h : Relation.ReflTransGen (Edge T) r v) :
    ¬ Relation.TransGen (Edge T) v v := by
  induction h with
  | refl =>
    intro hc
    obtain ⟨c, _, hc⟩ := Relation.TransGen.tail'_iff.mp hc
    exact hroot _ hc rfl
  | @tail u v _ huv ih =>
    intro hc
    obtain ⟨w, hvw, hwv⟩ := Relation.TransGen.tail'_iff.mp hc
    have hwu : w = u := PB2_parent_unique hroot huniq hwv huv
    subst hwu
    exact ih (Relation.TransGen.head' huv hvw)

lemma PB2_anc_edge {u v x : ℕ} (huv : (u, v) ∈ T) :
    Relation.ReflTransGen (Edge T) x v ↔ x = v ∨ Relation.ReflTransGen (Edge T) x u := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hxc, hcv⟩
    · exact Or.inl h.symm
    · have hcu : c = u := PB2_parent_unique hroot huniq hcv huv
      subst hcu
      exact Or.inr hxc
  · rintro (h | h)
    · subst h; exact Relation.ReflTransGen.refl
    · exact h.tail huv

lemma PB2_path_edge {a b : ℕ} (hab : (a, b) ∈ T) :
    pathTo T b = insert (a, b) (pathTo T a) := by
  ext e
  simp only [pathTo, Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨heT, heb⟩
    rcases (PB2_anc_edge hroot huniq hab).mp heb with h | h
    · left
      have h1 : e.1 = a := PB2_parent_unique hroot huniq (h ▸ heT) hab
      exact Prod.ext h1 h
    · exact Or.inr ⟨heT, h⟩
  · rintro (h | ⟨heT, hea⟩)
    · subst h; exact ⟨hab, Relation.ReflTransGen.refl⟩
    · exact ⟨heT, hea.tail hab⟩

include hreach

lemma PB2_depth_edge {a b : ℕ} (hab : (a, b) ∈ T) : depth T b = depth T a + 1 := by
  unfold depth
  rw [PB2_path_edge hroot huniq hab, Finset.card_insert_of_notMem]
  intro hmem
  simp only [pathTo, Finset.mem_filter] at hmem
  exact PB2_no_cycle hroot huniq (hreach b (PB2_mem_V_snd hab))
    (Relation.TransGen.tail' hmem.2 hab)

lemma PB2_depth_mono {x y : ℕ} (h : Relation.ReflTransGen (Edge T) x y) :
    depth T x ≤ depth T y := by
  induction h with
  | refl => exact le_refl _
  | @tail u v _ huv ih =>
    rw [PB2_depth_edge hroot huniq hreach huv]
    omega

omit huniq hreach in
lemma PB2_pathTo_root : pathTo T r = ∅ := by
  ext e
  simp only [pathTo, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
  intro heT her
  exact hroot e heT (PB2_to_root hroot her)

lemma PB2_depth_inj {v : ℕ} (h : Relation.ReflTransGen (Edge T) r v) :
    ∀ a b, Relation.ReflTransGen (Edge T) a v → Relation.ReflTransGen (Edge T) b v →
      depth T a = depth T b → a = b := by
  induction h with
  | refl =>
    intro a b ha hb _
    rw [PB2_to_root hroot ha, PB2_to_root hroot hb]
  | @tail u v _ huv ih =>
    intro a b ha hb hd
    have hdv := PB2_depth_edge hroot huniq hreach huv
    rcases (PB2_anc_edge hroot huniq huv).mp ha with ha' | ha' <;>
      rcases (PB2_anc_edge hroot huniq huv).mp hb with hb' | hb'
    · rw [ha', hb']
    · have := PB2_depth_mono hroot huniq hreach hb'
      subst ha'; omega
    · have := PB2_depth_mono hroot huniq hreach ha'
      subst hb'; omega
    · exact ih a b ha' hb' hd

omit hroot huniq hreach in
lemma PB2_treeChain_succ (n : ℕ) :
    treeChain (n + 1) = insert (n + 1, n + 1 + 1) (treeChain n) := by
  ext ⟨x, y⟩
  simp only [treeChain, Finset.mem_image, Finset.mem_Icc, Finset.mem_insert, Prod.mk.injEq]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, rfl, rfl⟩
    by_cases hi : i = n + 1
    · left; subst hi; exact ⟨rfl, rfl⟩
    · right; exact ⟨i, ⟨h1, by omega⟩, rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨i, ⟨h1, h2⟩, rfl, rfl⟩)
    · exact ⟨n + 1, ⟨by omega, le_refl _⟩, rfl, rfl⟩
    · exact ⟨i, ⟨h1, by omega⟩, rfl, rfl⟩

lemma PB2_image_chain {v : ℕ} (h : Relation.ReflTransGen (Edge T) r v) :
    (pathTo T v).image (fun x => (depth T x.1, depth T x.2)) = treeChain (depth T v - 1) := by
  induction h with
  | refl =>
    rw [PB2_pathTo_root hroot]
    simp [depth, PB2_pathTo_root hroot, treeChain]
  | @tail u v _ huv ih =>
    rw [PB2_path_edge hroot huniq huv, Finset.image_insert, ih,
      PB2_depth_edge hroot huniq hreach huv]
    have h1 : 1 ≤ depth T u := by unfold depth; omega
    obtain ⟨n, hn⟩ : ∃ n, depth T u = n + 1 := ⟨depth T u - 1, by omega⟩
    rw [hn, Nat.add_sub_cancel, Nat.add_sub_cancel, PB2_treeChain_succ]

end Tree

lemma PB2_perm_extend (f : ℕ → ℕ) :
    ∀ S : Finset ℕ, Set.InjOn f S → ∃ π : ℕ ≃ ℕ, ∀ x ∈ S, π x = f x := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; exact ⟨Equiv.refl ℕ, by simp⟩
  | @insert a S ha ih =>
    intro hinj
    obtain ⟨π, hπ⟩ := ih (hinj.mono (by simp))
    refine ⟨π.trans (Equiv.swap (π a) (f a)), ?_⟩
    intro x hx
    simp only [Equiv.trans_apply]
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Equiv.swap_apply_left _ _
    · have hxa : x ≠ a := fun h => ha (h ▸ hx)
      rw [hπ x hx]
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h
        rw [← hπ x hx] at h
        exact hxa (π.injective h)
      · intro h
        exact hxa (hinj (by simp [hx]) (by simp) h)

lemma PB2_mem_V_path {T : Finset (ℕ × ℕ)} {k v : ℕ} (hv : v ∈ V (pathTo T k)) :
    Relation.ReflTransGen (Edge T) v k ∧ v ∈ V T := by
  unfold V at hv
  rcases Finset.mem_union.mp hv with h | h <;> obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h <;>
    simp only [pathTo, Finset.mem_filter] at hx
  · exact ⟨Relation.ReflTransGen.head hx.1 hx.2, PB2_mem_V_fst hx.1⟩
  · exact ⟨hx.2, PB2_mem_V_snd hx.1⟩

lemma PB2_isTree_path {T : Finset (ℕ × ℕ)} (hT : IsTree T) {j k : ℕ} (hjk : (j, k) ∈ T) :
    IsTree (pathTo T k) := by
  obtain ⟨r, _, hroot, huniq, hreach⟩ := hT
  have hsub : pathTo T k ⊆ T := by
    intro x hx; simp only [pathTo, Finset.mem_filter] at hx; exact hx.1
  -- edges of `T` reached from the root along `T` towards `k` all lie in `pathTo T k`
  have hreachP : ∀ w, Relation.ReflTransGen (Edge T) r w → Relation.ReflTransGen (Edge T) w k →
      Relation.ReflTransGen (Edge (pathTo T k)) r w := by
    intro w hw
    induction hw with
    | refl => intro _; exact Relation.ReflTransGen.refl
    | @tail u v _ huv ih =>
      intro hvk
      have huP : (u, v) ∈ pathTo T k := by
        simp only [pathTo, Finset.mem_filter]; exact ⟨huv, hvk⟩
      exact (ih (Relation.ReflTransGen.head huv hvk)).tail huP
  have hrk : Relation.ReflTransGen (Edge T) r k := hreach k (PB2_mem_V_snd hjk)
  refine ⟨r, ?_, fun e he => hroot e (hsub he), ?_, ?_⟩
  · rcases Relation.ReflTransGen.cases_head hrk with h | ⟨c, hrc, hck⟩
    · exact absurd h.symm (hroot _ hjk)
    · apply PB2_mem_V_fst (b := c)
      simp only [pathTo, Finset.mem_filter]; exact ⟨hrc, hck⟩
  · intro v hv hvr
    obtain ⟨hvk, hvT⟩ := PB2_mem_V_path hv
    obtain ⟨u, hu, huu⟩ := huniq v hvT hvr
    refine ⟨u, ?_, fun u' hu' => huu u' (hsub hu')⟩
    simp only [pathTo, Finset.mem_filter]; exact ⟨hu, hvk⟩
  · intro v hv
    obtain ⟨hvk, hvT⟩ := PB2_mem_V_path hv
    exact hreachP v (hreach v hvT) hvk

/-- (B2) Relabelling the root-to-`e.2` path as the chain `T_{[e.1]}`. -/
theorem phi_path_chain (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ) (hφ : IsTreeRule φ)
    {T : Finset (ℕ × ℕ)} (hT : IsTree T) {e : ℕ × ℕ} (he : e ∈ T) :
    ∀ i ∈ N (pathTo T e.2), φ (pathTo T e.2) (unitLoss e) i =
      φ (treeChain (depth T e.1)) (chainLoss (depth T e.1)) (depth T i) := by
  classical
  have he' : (e.1, e.2) ∈ T := he
  have hP : IsTree (pathTo T e.2) := PB2_isTree_path hT he'
  obtain ⟨r, _, hroot, huniq, hreach⟩ := hT
  have hrk : Relation.ReflTransGen (Edge T) r e.2 := hreach _ (PB2_mem_V_snd he')
  have hinj : Set.InjOn (depth T) (V (pathTo T e.2) : Set ℕ) := by
    intro a ha b hb hab
    exact PB2_depth_inj hroot huniq hreach hrk a b (PB2_mem_V_path ha).1
      (PB2_mem_V_path hb).1 hab
  obtain ⟨π, hπ⟩ := PB2_perm_extend (depth T) (V (pathTo T e.2)) hinj
  have heP : e ∈ pathTo T e.2 := by
    simp only [pathTo, Finset.mem_filter]; exact ⟨he, Relation.ReflTransGen.refl⟩
  have hfstV : ∀ x ∈ pathTo T e.2, x.1 ∈ V (pathTo T e.2) := fun x hx =>
    PB2_mem_V_fst (b := x.2) hx
  have hsndV : ∀ x ∈ pathTo T e.2, x.2 ∈ V (pathTo T e.2) := fun x hx =>
    PB2_mem_V_snd (a := x.1) hx
  have hrel : relabel π (pathTo T e.2) = treeChain (depth T e.1) := by
    unfold relabel
    rw [Finset.map_eq_image]
    rw [Finset.image_congr (g := fun x => (depth T x.1, depth T x.2))]
    · rw [PB2_image_chain hroot huniq hreach hrk, PB2_depth_edge hroot huniq hreach he']
      simp
    · intro x hx
      simp only [Equiv.toEmbedding_apply, Equiv.prodCongr_apply, Prod.map]
      rw [hπ x.1 (hfstV x hx), hπ x.2 (hsndV x hx)]
  have hunit : IsTreeLoss (unitLoss e) := by
    intro x; unfold unitLoss; split_ifs <;> norm_num
  have hchain : IsTreeLoss (chainLoss (depth T e.1)) := by
    intro x; unfold chainLoss; split_ifs <;> norm_num
  have hloss : ∀ x ∈ pathTo T e.2,
      chainLoss (depth T e.1) (π x.1, π x.2) = unitLoss e x := by
    intro x hx
    rw [hπ x.1 (hfstV x hx), hπ x.2 (hsndV x hx)]
    unfold chainLoss unitLoss
    by_cases hxe : x = e
    · subst hxe
      rw [PB2_depth_edge hroot huniq hreach he']
      simp
    · rw [if_neg hxe, if_neg]
      intro h
      simp only [Prod.mk.injEq] at h
      apply hxe
      have h1 : x.1 = e.1 := hinj (hfstV x hx) (hfstV e heP) h.1
      have h2 : x.2 = e.2 := hinj (hsndV x hx) (hsndV e heP)
        (by rw [h.2, PB2_depth_edge hroot huniq hreach he'])
      exact Prod.ext h1 h2
  have h3 := (hφ _ hP (unitLoss e) hunit).2.2.1 π (chainLoss (depth T e.1)) hchain hloss
  intro i hi
  rw [h3 i hi, hrel]
  have hiV : i ∈ V (pathTo T e.2) := by unfold V N at *; exact Finset.mem_union_left _ hi
  rw [hπ i hiV]

/-! ### PartC -/
lemma PC_fst_mem_V {T : Finset (ℕ × ℕ)} {a b : ℕ} (h : (a, b) ∈ T) : a ∈ V T := by
  unfold V
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(a, b), h, rfl⟩)

lemma PC_snd_mem_V {T : Finset (ℕ × ℕ)} {a b : ℕ} (h : (a, b) ∈ T) : b ∈ V T := by
  unfold V
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(a, b), h, rfl⟩)

lemma PC_N_sub_V {T : Finset (ℕ × ℕ)} {i : ℕ} (h : i ∈ N T) : i ∈ V T := by
  unfold N at h
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp h
  exact PC_fst_mem_V hab

/-- In a tree, every vertex has at most one parent. -/
lemma PC_unique_parent {T : Finset (ℕ × ℕ)} (hT : IsTree T) {u u' v : ℕ}
    (h : (u, v) ∈ T) (h' : (u', v) ∈ T) : u = u' := by
  obtain ⟨r, -, hroot, huniq, -⟩ := hT
  have hv : v ∈ V T := PC_snd_mem_V h
  have hvr : v ≠ r := hroot _ h
  exact (huniq v hv hvr).unique h h'

lemma PC_mem_pathTo {T : Finset (ℕ × ℕ)} {v : ℕ} {f : ℕ × ℕ} :
    f ∈ pathTo T v ↔ f ∈ T ∧ Relation.ReflTransGen (Edge T) f.2 v := by
  unfold pathTo
  simp [Finset.mem_filter]

lemma PC_mem_subtreeAt {T : Finset (ℕ × ℕ)} {v : ℕ} {f : ℕ × ℕ} :
    f ∈ subtreeAt T v ↔ f ∈ T ∧ Relation.ReflTransGen (Edge T) v f.1 := by
  unfold subtreeAt
  simp [Finset.mem_filter]

theorem mem_N_pathTo_iff {T : Finset (ℕ × ℕ)} (hT : IsTree T) {e : ℕ × ℕ} (he : e ∈ T)
    {i : ℕ} (hi : i ∈ N T) :
    i ∈ N (pathTo T e.2) ↔ e ∈ subtreeAt T i := by
  obtain ⟨j, k⟩ := e
  simp only at *
  rw [PC_mem_subtreeAt]
  unfold N
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hf, rfl⟩
    rw [PC_mem_pathTo] at hf
    obtain ⟨hab, hbk⟩ := hf
    refine ⟨he, ?_⟩
    simp only at hbk ⊢
    rcases hbk.cases_tail with hbk | ⟨c, hbc, hck⟩
    · subst hbk
      rw [PC_unique_parent hT hab he]
    · have hcj : c = j := PC_unique_parent hT hck he
      subst hcj
      exact Relation.ReflTransGen.head hab hbc
  · rintro ⟨-, hij⟩
    simp only at hij
    rcases hij.cases_head with hij | ⟨c, hic, hcj⟩
    · subst hij
      exact ⟨(i, k), PC_mem_pathTo.mpr ⟨he, Relation.ReflTransGen.refl⟩, rfl⟩
    · refine ⟨(i, c), PC_mem_pathTo.mpr ⟨hic, ?_⟩, rfl⟩
      exact hcj.tail he

/-- Facts about adding a new leaf edge `e` with `e.2 ∉ V T`: the new leaf has no outgoing edge,
and reachability to any other vertex is unchanged. -/
lemma PC_leaf_no_out {T : Finset (ℕ × ℕ)} {e : ℕ × ℕ} (hins : IsTree (insert e T))
    (hnew : e.2 ∉ V T) {x : ℕ} : (e.2, x) ∉ insert e T := by
  obtain ⟨a, w⟩ := e
  simp only at hnew ⊢
  intro hx
  rcases Finset.mem_insert.mp hx with hx | hx
  · -- `e = (w, w)` is a self-loop: impossible in a tree.
    obtain ⟨rfl, -⟩ := Prod.mk.inj hx
    obtain ⟨r, hrV, hroot, -, hreach⟩ := hins
    have hwV : w ∈ V (insert (w, w) T) := PC_snd_mem_V (Finset.mem_insert_self _ _)
    have key : ∀ y, Relation.ReflTransGen (Edge (insert (w, w) T)) r y → y = w → r = w := by
      intro y hy
      induction hy with
      | refl => exact id
      | tail _ hbc ih =>
        intro hc
        subst hc
        apply ih
        rcases Finset.mem_insert.mp hbc with h | h
        · exact (Prod.mk.inj h).1
        · exact absurd (PC_snd_mem_V h) hnew
    exact hroot (w, w) (Finset.mem_insert_self _ _) (key w (hreach w hwV) rfl).symm
  · exact hnew (PC_fst_mem_V hx)

lemma PC_reach_from_leaf {T : Finset (ℕ × ℕ)} {e : ℕ × ℕ} (hins : IsTree (insert e T))
    (hnew : e.2 ∉ V T) {v : ℕ} (hv : v ∈ V T) :
    ¬ Relation.ReflTransGen (Edge (insert e T)) e.2 v := by
  intro h
  rcases h.cases_head with h | ⟨c, hc, -⟩
  · exact hnew (h ▸ hv)
  · exact PC_leaf_no_out hins hnew hc

lemma PC_reach_iff {T : Finset (ℕ × ℕ)} {e : ℕ × ℕ} (hnew : e.2 ∉ V T) {x y : ℕ}
    (hy : y ≠ e.2) :
    Relation.ReflTransGen (Edge (insert e T)) x y ↔ Relation.ReflTransGen (Edge T) x y := by
  constructor
  · intro h
    revert hy
    induction h with
    | refl => exact fun _ => Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      intro hc
      rcases Finset.mem_insert.mp hbc with h | h
      · exact absurd (by rw [← h]) hc
      · have hb : b ≠ e.2 := fun hb => hnew (hb ▸ PC_fst_mem_V h)
        exact (ih hb).tail h
  · intro h
    exact Relation.ReflTransGen.mono (fun a b h => Finset.mem_insert_of_mem h) _ _ h

lemma PC_depth_eq {T : Finset (ℕ × ℕ)} {e : ℕ × ℕ} (hins : IsTree (insert e T))
    (hnew : e.2 ∉ V T) {v : ℕ} (hv : v ∈ V T) : depth (insert e T) v = depth T v := by
  have hvw : v ≠ e.2 := fun h => hnew (h ▸ hv)
  have hpath : pathTo (insert e T) v = pathTo T v := by
    ext f
    rw [PC_mem_pathTo, PC_mem_pathTo, PC_reach_iff hnew hvw, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hf, hr⟩
      · exact absurd ((PC_reach_iff hnew hvw).mpr hr) (PC_reach_from_leaf hins hnew hv)
      · exact ⟨hf, hr⟩
    · rintro ⟨hf, hr⟩
      exact ⟨Or.inr hf, hr⟩
  unfold depth
  rw [hpath]

theorem formula_zero_truncation (c : ℕ → ℕ → ℝ) {T : Finset (ℕ × ℕ)} (hT : IsTree T)
    {e : ℕ × ℕ} (hins : IsTree (insert e T)) (hnew : e.2 ∉ V T) {ℓ : ℕ × ℕ → ℝ}
    (hℓe : ℓ e = 0) {i : ℕ} (hi : i ∈ N T) :
    ∑ e' ∈ subtreeAt T i, ℓ e' * c (depth T e'.1) (depth T i) =
      ∑ e' ∈ subtreeAt (insert e T) i, ℓ e' * c (depth (insert e T) e'.1) (depth (insert e T) i) := by
  have heT : e ∉ T := fun h => hnew (by obtain ⟨a, w⟩ := e; exact PC_snd_mem_V h)
  have hiV : i ∈ V T := PC_N_sub_V hi
  -- membership in the new subtree
  have hmem : ∀ f, f ∈ subtreeAt (insert e T) i ↔
      f ∈ subtreeAt T i ∨ (f = e ∧ e ∈ subtreeAt (insert e T) i) := by
    intro f
    constructor
    · intro hf
      rw [PC_mem_subtreeAt] at hf
      obtain ⟨hf, hr⟩ := hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact Or.inr ⟨rfl, PC_mem_subtreeAt.mpr ⟨Finset.mem_insert_self _ _, hr⟩⟩
      · have h1 : f.1 ≠ e.2 := fun h =>
          hnew (h ▸ by obtain ⟨a, b⟩ := f; exact PC_fst_mem_V hf)
        exact Or.inl (PC_mem_subtreeAt.mpr ⟨hf, (PC_reach_iff hnew h1).mp hr⟩)
    · rintro (hf | ⟨rfl, hf⟩)
      · rw [PC_mem_subtreeAt] at hf ⊢
        obtain ⟨hf, hr⟩ := hf
        have h1 : f.1 ≠ e.2 := fun h =>
          hnew (h ▸ by obtain ⟨a, b⟩ := f; exact PC_fst_mem_V hf)
        exact ⟨Finset.mem_insert_of_mem hf, (PC_reach_iff hnew h1).mpr hr⟩
      · exact hf
  have hterm : ∀ f ∈ subtreeAt T i,
      ℓ f * c (depth T f.1) (depth T i) =
        ℓ f * c (depth (insert e T) f.1) (depth (insert e T) i) := by
    intro f hf
    have hfT : f ∈ T := (PC_mem_subtreeAt.mp hf).1
    have h1 : f.1 ∈ V T := by obtain ⟨a, b⟩ := f; exact PC_fst_mem_V hfT
    rw [PC_depth_eq hins hnew h1, PC_depth_eq hins hnew hiV]
  have heS : e ∉ subtreeAt T i := fun h => heT (PC_mem_subtreeAt.mp h).1
  by_cases he : e ∈ subtreeAt (insert e T) i
  · have hS : subtreeAt (insert e T) i = insert e (subtreeAt T i) := by
      ext f
      rw [hmem, Finset.mem_insert]
      constructor
      · rintro (h | ⟨h, -⟩)
        · exact Or.inr h
        · exact Or.inl h
      · rintro (h | h)
        · exact Or.inr ⟨h, he⟩
        · exact Or.inl h
    rw [hS, Finset.sum_insert heS, hℓe, zero_mul, zero_add]
    exact Finset.sum_congr rfl hterm
  · have hS : subtreeAt (insert e T) i = subtreeAt T i := by
      ext f
      rw [hmem]
      constructor
      · rintro (h | ⟨-, h⟩)
        · exact h
        · exact absurd h he
      · exact Or.inl
    rw [hS]
    exact Finset.sum_congr rfl hterm

end SeqLossP3

open SeqLossP3

theorem solution (φ : Finset (ℕ × ℕ) → (ℕ × ℕ → ℝ) → ℕ → ℝ)
    (hφ : IsTreeRule φ) :
    (TreeAdditive φ ∧ TreeZeroTruncation φ) ↔
      ∀ T, IsTree T → ∀ ℓ, IsTreeLoss ℓ → ∀ i ∈ N T,
        φ T ℓ i = ∑ e ∈ subtreeAt T i,
          ℓ e * φ (treeChain (depth T e.1)) (chainLoss (depth T e.1)) (depth T i) := by
  classical
  constructor
  · rintro ⟨hadd, hzt⟩ T hT ℓ hℓ i hi
    rw [phi_decomp φ hφ hadd hT hℓ i hi]
    have hsub : subtreeAt T i ⊆ T := by
      unfold subtreeAt; exact Finset.filter_subset _ _
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl (fun e he => ?_)
      have heT : e ∈ T := hsub he
      obtain ⟨-, hpr⟩ := phi_unit_prune φ hφ hzt hT heT
      rw [hpr i hi, if_pos ((mem_N_pathTo_iff hT heT hi).2 he),
        phi_path_chain φ hφ hT heT i ((mem_N_pathTo_iff hT heT hi).2 he)]
    · intro e heT he
      obtain ⟨-, hpr⟩ := phi_unit_prune φ hφ hzt hT heT
      rw [hpr i hi, if_neg (fun h => he ((mem_N_pathTo_iff hT heT hi).1 h)), mul_zero]
  · intro hf
    refine ⟨fun T hT ℓ ℓ' hℓ hℓ' i hi => ?_, fun T hT ℓ hℓ e hins hnew hℓe i hi => ?_⟩
    · have hℓℓ' : IsTreeLoss (ℓ + ℓ') := fun e => add_nonneg (hℓ e) (hℓ' e)
      rw [hf T hT ℓ hℓ i hi, hf T hT ℓ' hℓ' i hi, hf T hT (ℓ + ℓ') hℓℓ' i hi,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      simp only [Pi.add_apply]; ring
    · have hiN : i ∈ N (insert e T) := by
        unfold N at hi ⊢; rw [Finset.image_insert]; exact Finset.mem_insert_of_mem hi
      rw [hf T hT ℓ hℓ i hi, hf (insert e T) hins ℓ hℓ i hiN]
      exact formula_zero_truncation (fun m t => φ (treeChain m) (chainLoss m) t) hT hins hnew
        hℓe hi
